import Mathlib

/-!
# 布尔电路 DAG 组件

本文件提供一个可复用的布尔电路组件，采用“按拓扑顺序构造节点”的方式表示 DAG。

这种表示的优点是：

- 共享子表达式天然可表示，因此不是树；
- 无环性由类型保证：新节点只能引用输入线或先前已经存在的节点；
- 求值函数可以直接按节点顺序递归定义。

当前支持的门类型：

- 左方输入 `inputL`
- 右方输入 `inputR`
- 异或门 `xor`
- 与门 `and`
- 非门 `not`
-/

namespace LeanCryptoProtocols.Circuit

/-- 电路中的引用：可以指向左输入、右输入或更早的门输出。 -/
inductive Ref (nLeft nRight nGates : Nat) where
  | inputL : Fin nLeft → Ref nLeft nRight nGates
  | inputR : Fin nRight → Ref nLeft nRight nGates
  | gate : Fin nGates → Ref nLeft nRight nGates
  deriving DecidableEq, Repr

/-- 一个新门只能引用当前已经存在的线。 -/
inductive Node (nLeft nRight nGates : Nat) where
  | xor : Ref nLeft nRight nGates → Ref nLeft nRight nGates → Node nLeft nRight nGates
  | and : Ref nLeft nRight nGates → Ref nLeft nRight nGates → Node nLeft nRight nGates
  | not : Ref nLeft nRight nGates → Node nLeft nRight nGates
  deriving DecidableEq, Repr

/--
按拓扑顺序构造的门序列。

`Program nLeft nRight n` 表示一个含有 `n` 个内部门的 DAG。
-/
inductive Program (nLeft nRight : Nat) : Nat → Type where
  | nil : Program nLeft nRight 0
  | snoc : Program nLeft nRight n → Node nLeft nRight n → Program nLeft nRight (n + 1)
  deriving Repr

/-- 单输出布尔电路。 -/
structure BoolCircuit where
  nLeft : Nat
  nRight : Nat
  nGates : Nat
  program : Program nLeft nRight nGates
  output : Ref nLeft nRight nGates
  deriving Repr

/-- 电路输入。 -/
structure Inputs (c : BoolCircuit) where
  left : Fin c.nLeft → Bool
  right : Fin c.nRight → Bool

/-- 读取引用对应的布尔值。 -/
def evalRef {nLeft nRight nGates : Nat}
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool)
    (gateVals : Fin nGates → Bool) :
    Ref nLeft nRight nGates → Bool
  | .inputL i => leftIn i
  | .inputR j => rightIn j
  | .gate k => gateVals k

/-- 计算单个门的输出。 -/
def evalNode {nLeft nRight nGates : Nat}
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool)
    (gateVals : Fin nGates → Bool) :
    Node nLeft nRight nGates → Bool
  | .xor a b => Bool.xor (evalRef leftIn rightIn gateVals a) (evalRef leftIn rightIn gateVals b)
  | .and a b => evalRef leftIn rightIn gateVals a && evalRef leftIn rightIn gateVals b
  | .not a => !(evalRef leftIn rightIn gateVals a)

/-- 在已有门赋值尾部追加一个新门的值。 -/
def extendGateVals {n : Nat}
    (prev : Fin n → Bool) (next : Bool) : Fin (n + 1) → Bool
  | ⟨i, _⟩ =>
      if h : i < n then
        prev ⟨i, h⟩
      else
        next

/-- 递归计算整个门序列的所有门输出。 -/
def Program.eval {nLeft nRight nGates : Nat}
    (program : Program nLeft nRight nGates)
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool) :
    Fin nGates → Bool :=
  match program with
  | .nil => Fin.elim0
  | .snoc prev node =>
      let prevVals := prev.eval leftIn rightIn
      let next := evalNode leftIn rightIn prevVals node
      extendGateVals prevVals next

/-- 电路求值。 -/
def BoolCircuit.eval (c : BoolCircuit) (input : Inputs c) : Bool :=
  evalRef input.left input.right (c.program.eval input.left input.right) c.output

@[simp] theorem evalRef_inputL {nLeft nRight nGates : Nat}
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool) (gateVals : Fin nGates → Bool)
    (i : Fin nLeft) :
    evalRef leftIn rightIn gateVals (.inputL i) = leftIn i := by
  rfl

@[simp] theorem evalRef_inputR {nLeft nRight nGates : Nat}
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool) (gateVals : Fin nGates → Bool)
    (j : Fin nRight) :
    evalRef leftIn rightIn gateVals (.inputR j) = rightIn j := by
  rfl

@[simp] theorem evalRef_gate {nLeft nRight nGates : Nat}
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool) (gateVals : Fin nGates → Bool)
    (k : Fin nGates) :
    evalRef leftIn rightIn gateVals (.gate k) = gateVals k := by
  rfl

@[simp] theorem extendGateVals_last {n : Nat} (prev : Fin n → Bool) (next : Bool) :
    extendGateVals prev next (Fin.last n) = next := by
  simp [extendGateVals, Fin.last]

theorem extendGateVals_castSucc {n : Nat} (prev : Fin n → Bool) (next : Bool) (i : Fin n) :
    extendGateVals prev next i.castSucc = prev i := by
  simp [extendGateVals, i.is_lt]

/-- 新增节点的值恰好等于在旧赋值下对该节点求值。 -/
theorem Program.eval_snoc_last {nLeft nRight n : Nat}
    (program : Program nLeft nRight n)
    (node : Node nLeft nRight n)
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool) :
    (Program.eval (.snoc program node) leftIn rightIn) (Fin.last n) =
      evalNode leftIn rightIn (program.eval leftIn rightIn) node := by
  simp [Program.eval, extendGateVals_last]

/-- 旧节点在尾部追加新节点后，其值保持不变。 -/
theorem Program.eval_snoc_castSucc {nLeft nRight n : Nat}
    (program : Program nLeft nRight n)
    (node : Node nLeft nRight n)
    (leftIn : Fin nLeft → Bool) (rightIn : Fin nRight → Bool)
    (i : Fin n) :
    (Program.eval (.snoc program node) leftIn rightIn) i.castSucc =
      (program.eval leftIn rightIn) i := by
  simp [Program.eval, extendGateVals_castSucc]

end LeanCryptoProtocols.Circuit

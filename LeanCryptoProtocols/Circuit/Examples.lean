import LeanCryptoProtocols.Circuit.BoolCircuit

/-!
# 布尔电路示例

本文件给出若干最小示例电路，用于测试独立的 DAG 电路组件。
-/

namespace LeanCryptoProtocols.Circuit

/-- 单个 XOR 门。 -/
def xorExample : BoolCircuit where
  nLeft := 1
  nRight := 1
  nGates := 1
  program := .snoc .nil (.xor (.inputL ⟨0, by decide⟩) (.inputR ⟨0, by decide⟩))
  output := .gate ⟨0, by decide⟩

/-- 单个 AND 门。 -/
def andExample : BoolCircuit where
  nLeft := 1
  nRight := 1
  nGates := 1
  program := .snoc .nil (.and (.inputL ⟨0, by decide⟩) (.inputR ⟨0, by decide⟩))
  output := .gate ⟨0, by decide⟩

/-- 单个 NOT 门。 -/
def notExample : BoolCircuit where
  nLeft := 1
  nRight := 0
  nGates := 1
  program := .snoc .nil (.not (.inputL ⟨0, by decide⟩))
  output := .gate ⟨0, by decide⟩

/--
含共享子表达式的 DAG 示例：

- `g0 = x xor y`
- `g1 = not g0`
- `g2 = g0 and g1`

其中 `g0` 被后续两个节点共同引用，因此这是 DAG 而不是树。
-/
def sharedDagExample : BoolCircuit where
  nLeft := 1
  nRight := 1
  nGates := 3
  program :=
    .snoc
      (.snoc
        (.snoc .nil (.xor (.inputL ⟨0, by decide⟩) (.inputR ⟨0, by decide⟩)))
        (.not (.gate ⟨0, by decide⟩)))
      (.and (.gate ⟨0, by decide⟩) (.gate ⟨1, by decide⟩))
  output := .gate ⟨2, by decide⟩

/-- 一个更普通的混合 DAG。 -/
def mixedExample : BoolCircuit where
  nLeft := 2
  nRight := 1
  nGates := 3
  program :=
    .snoc
      (.snoc
        (.snoc .nil (.xor (.inputL ⟨0, by decide⟩) (.inputR ⟨0, by decide⟩)))
        (.and (.gate ⟨0, by decide⟩) (.inputL ⟨1, by decide⟩)))
      (.not (.gate ⟨1, by decide⟩))
  output := .gate ⟨2, by decide⟩

@[simp] theorem xorExample_eval (x y : Bool) :
    xorExample.eval
      ⟨fun _ => x, fun _ => y⟩ = Bool.xor x y := by
  cases x <;> cases y <;> rfl

@[simp] theorem andExample_eval (x y : Bool) :
    andExample.eval
      ⟨fun _ => x, fun _ => y⟩ = (x && y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem notExample_eval (x : Bool) :
    notExample.eval
      ⟨fun _ => x, Fin.elim0⟩ = !x := by
  cases x <;> rfl

@[simp] theorem sharedDagExample_eval (x y : Bool) :
    sharedDagExample.eval
      ⟨fun _ => x, fun _ => y⟩ = (Bool.xor x y && !(Bool.xor x y)) := by
  cases x <;> cases y <;> rfl

@[simp] theorem mixedExample_eval (x₀ x₁ y : Bool) :
    mixedExample.eval
      ⟨(fun i => if i = ⟨0, by decide⟩ then x₀ else x₁), fun _ => y⟩ =
      !(Bool.xor x₀ y && x₁) := by
  cases x₀ <;> cases x₁ <;> cases y <;> rfl

end LeanCryptoProtocols.Circuit

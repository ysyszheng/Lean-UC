import Mathlib

/-!
# Canetti Section 2 风格的 machine / protocol 建模

本文件按 Canetti 2000 第 2 节的简化模型，给出本项目新的静态结构层：

- machine identity；
- communication set；
- machine program；
- protocol shape；
- caller / subroutine 的身份关系。

这里先只刻画“协议长什么样”，而不在本文件里定义 UC 安全或组合定理。
-/

universe u v

namespace LeanCryptoProtocols.UC

/-- machine identity。用列表表示层级化身份前缀。 -/
abbrev MachineId : Type := List Nat

/-- 环境的固定身份。 -/
def envId : MachineId := []

/-- 敌手的固定身份。 -/
def advId : MachineId := [1]

/-- 前缀关系：`x` 是 `y` 的前缀。 -/
def IsPrefix (x y : MachineId) : Prop :=
  ∃ suffix, y = x ++ suffix

/-- 真前缀关系。 -/
def IsProperPrefix (x y : MachineId) : Prop :=
  IsPrefix x y ∧ x ≠ y

/-- `caller` 是 `callee` 的直接调用者。 -/
def IsCallerOf (caller callee : MachineId) : Prop :=
  ∃ idx, callee = caller ++ [idx]

/-- `callee` 是 `caller` 的直接 subroutine。 -/
def IsSubroutineOf (callee caller : MachineId) : Prop :=
  IsCallerOf caller callee

@[simp] theorem isPrefix_refl (x : MachineId) : IsPrefix x x := by
  refine ⟨[], ?_⟩
  simp

/-- communication set 中的标准端口标签。 -/
inductive PortLabel where
  | input
  | subroutineOutput
  | backdoor
  deriving Repr, DecidableEq, Inhabited

/-- 一个端口由拥有该端口的 machine identity 和标签组成。 -/
structure CommPort where
  owner : MachineId
  label : PortLabel
  deriving Repr, DecidableEq, Inhabited

/-- 在 machine 之间路由的消息。 -/
structure Envelope (Payload : Type u) where
  sender : CommPort
  receiver : CommPort
  payload : Payload
  deriving Repr, DecidableEq

/-- 一次原子激活后的结果：更新状态，并至多发送一条消息。 -/
structure ActivationResult (Payload : Type u) (State : Type v) where
  state : State
  outgoing? : Option (Envelope Payload)
  deriving Repr, DecidableEq

/--
machine 的局部程序。

这里把局部状态类型封装在程序对象里；协议建模者需要写的是：

- 初始状态；
- 收到一条消息后的状态更新与至多一条待发送消息；
- 局部输出提取函数。
-/
structure MachineProgram (Payload : Type u) (Out : Type v) where
  LocalState : Type v
  init : LocalState
  step :
    LocalState →
    Envelope Payload →
    PMF (ActivationResult Payload LocalState)
  output : LocalState → Out

/-- 一个 machine 由身份、communication set 和局部程序组成。 -/
structure Machine (Payload : Type u) (Out : Type v) where
  id : MachineId
  communicationSet : Finset CommPort
  program : MachineProgram Payload Out

/-- 抹去输出类型后的 machine。 -/
abbrev AnyMachine (Payload : Type u) :=
  Σ Out : Type, Machine Payload Out

/-- 从异质机器中抽取 identity。 -/
def AnyMachine.id {Payload : Type u} (m : AnyMachine Payload) : MachineId :=
  m.2.id

/-- 抽取 protocol 中所有 machine identity。 -/
def machineIds {Payload : Type u}
    (machines : List (AnyMachine Payload)) : List MachineId :=
  machines.map AnyMachine.id

/--
protocol 的静态外形。

本项目在这一层只记录 Section 2 里对 protocol shape 必需的静态约束；
真正的执行分布在 `Security.lean` 中由 `ExecutableProtocol` 给出。
-/
structure ProtocolShape (Payload : Type u) where
  machines : List (AnyMachine Payload)
  uniqueIds : (machineIds machines).Nodup
  callerSubroutineConsistent : Prop
  envSeparated : envId ∉ machineIds machines
  advSeparated : advId ∉ machineIds machines

/-- protocol 是否使用了某个给定 identity 作为 subroutine 槽位。 -/
def ProtocolShape.UsesSubroutine {Payload : Type u}
    (π : ProtocolShape Payload) (sid : MachineId) : Prop :=
  sid ∈ machineIds π.machines

/-- 一个协议是否只在给定前缀子树内引入新身份。 -/
def ProtocolShape.RootedAt {Payload : Type u}
    (π : ProtocolShape Payload) (root : MachineId) : Prop :=
  ∀ mid, mid ∈ machineIds π.machines → IsPrefix root mid

end LeanCryptoProtocols.UC

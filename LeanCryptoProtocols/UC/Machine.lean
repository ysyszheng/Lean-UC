import Mathlib

/-!
# Canetti Section 2 风格的 machine / protocol 建模

本文件按 Canetti 2000 第 2 节的简化模型，给出本项目新的静态结构层：

- machine identity；
- communication set；
- machine program；
- protocol shape；
- caller / subroutine / subsidiary 关系。

这里先只刻画“协议长什么样”，而不在本文件里定义 UC 安全或组合定理。
-/

universe u v

namespace LeanCryptoProtocols.UC

/-- machine identity。这里直接使用自然数，不在 identity 本身编码调用层级。 -/
abbrev MachineId : Type := Nat

/-- 环境的固定身份。 -/
def envId : MachineId := 0

/-- 敌手的固定身份。 -/
def advId : MachineId := 1

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

/-- machine 是否允许向某个 identity 的 `input` 端口发送消息。 -/
def CanSendInputTo {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (id : MachineId) : Prop :=
  ⟨id, .input⟩ ∈ μ.communicationSet

/-- machine 是否允许向某个 identity 的 `subroutineOutput` 端口发送消息。 -/
def CanSendSubroutineOutputTo {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (id : MachineId) : Prop :=
  ⟨id, .subroutineOutput⟩ ∈ μ.communicationSet

/-- machine 是否允许向某个 identity 的 `backdoor` 端口发送消息。 -/
def CanSendBackdoorTo {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (id : MachineId) : Prop :=
  ⟨id, .backdoor⟩ ∈ μ.communicationSet

/-- 若 `μ` 能向 `id` 的 `input` 端口发送，则称 `μ` 是 `id` 的 caller。 -/
def IsCallerOfId {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (id : MachineId) : Prop :=
  CanSendInputTo μ id

/-- 若 `μ` 能向 `id` 的 `subroutineOutput` 端口发送，则称 `μ` 是 `id` 的 subroutine。 -/
def IsSubroutineOfId {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (id : MachineId) : Prop :=
  CanSendSubroutineOutputTo μ id

/--
protocol 的静态外形。

本项目在这一层只记录 Section 2 里对 protocol shape 必需的静态约束；
真正的执行分布在 `Security.lean` 中由 `ExecutableProtocol` 给出。
-/
structure ProtocolShape (Payload : Type u) where
  machines : List (AnyMachine Payload)
  uniqueIds : (machineIds machines).Nodup
  callerHasMatchingSubroutine :
    ∀ m ∈ machines, ∀ id : MachineId,
      IsCallerOfId m.2 id →
      ∃ m' ∈ machines, AnyMachine.id m' = id ∧ IsSubroutineOfId m'.2 (AnyMachine.id m)
  subroutineHasMatchingCaller :
    ∀ m ∈ machines, ∀ id : MachineId,
      IsSubroutineOfId m.2 id →
      id ∈ machineIds machines → -- id还可能是external identity（例如环境、敌手），这里不要求它们在protocol里有machine。见Canetti 2000 Page 11.
      ∃ m' ∈ machines, AnyMachine.id m' = id ∧ IsCallerOfId m'.2 (AnyMachine.id m)
  envSeparated : envId ∉ machineIds machines
  advSeparated : advId ∉ machineIds machines

/-- protocol 中是否存在某个给定 identity 的 machine。 -/
def ProtocolShape.HasMachineId {Payload : Type u}
    (π : ProtocolShape Payload) (mid : MachineId) : Prop :=
  mid ∈ machineIds π.machines

/-- `parent` 是否拥有一个 id 为 `child` 的直接 subroutine。 -/
def ProtocolShape.MachineIsSubroutineOf {Payload : Type u}
    (π : ProtocolShape Payload) (child parent : MachineId) : Prop :=
  ∃ mChild ∈ π.machines, ∃ mParent ∈ π.machines,
    AnyMachine.id mChild = child ∧
    AnyMachine.id mParent = parent ∧
    IsSubroutineOfId mChild.2 parent

/-- `parent` 是否是 id 为 `child` 的 machine 的直接 caller。 -/
def ProtocolShape.MachineIsCallerOf {Payload : Type u}
    (π : ProtocolShape Payload) (parent child : MachineId) : Prop :=
  ∃ mParent ∈ π.machines, ∃ mChild ∈ π.machines,
    AnyMachine.id mParent = parent ∧
    AnyMachine.id mChild = child ∧
    IsCallerOfId mParent.2 child

/-- subsidiary 关系：通过 subroutine 关系的传递闭包得到。 -/
def ProtocolShape.MachineIsSubsidiaryOf {Payload : Type u}
    (π : ProtocolShape Payload) (child parent : MachineId) : Prop :=
  Relation.TransGen (ProtocolShape.MachineIsSubroutineOf π) child parent

/--
`id` 是 machine `μ` 相对于协议 `π` 的 external identity。

按 Canetti 第 2 节的表述，这意味着：

- `μ` 属于 `π`；
- `μ` 是 `id` 的 subroutine；
- `id` 不是 `π` 中任何 machine 的 identity。
-/
def ProtocolShape.IsExternalIdentityOf {Payload : Type u}
    (π : ProtocolShape Payload) (μ : AnyMachine Payload) (id : MachineId) : Prop :=
  μ ∈ π.machines ∧
  IsSubroutineOfId μ.2 id ∧
  id ∉ machineIds π.machines

/-- `mid` 是否是 `π` 的 main machine。 -/
def ProtocolShape.IsMainMachine {Payload : Type u}
    (π : ProtocolShape Payload) (mid : MachineId) : Prop :=
  ∃ μ ∈ π.machines, AnyMachine.id μ = mid ∧
    ∃ id, π.IsExternalIdentityOf μ id

/-- `mid` 是否是 `π` 的 internal machine。 -/
def ProtocolShape.IsInternalMachine {Payload : Type u}
    (π : ProtocolShape Payload) (mid : MachineId) : Prop :=
  π.HasMachineId mid ∧ ¬ π.IsMainMachine mid

/-- protocol 是否使用了某个给定 identity 作为 subroutine 槽位。 -/
def ProtocolShape.UsesSubroutine {Payload : Type u}
    (π : ProtocolShape Payload) (sid : MachineId) : Prop :=
  ∃ parent, π.MachineIsSubroutineOf sid parent

@[simp] theorem envId_eq_zero : envId = 0 := rfl

@[simp] theorem advId_eq_one : advId = 1 := rfl

end LeanCryptoProtocols.UC

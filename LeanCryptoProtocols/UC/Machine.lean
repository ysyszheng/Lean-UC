import Mathlib

/-!
# Canetti Section 2 风格的 machine / protocol 建模

本文件按 Canetti 2000 第 2 节的简化模型，给出本项目新的静态结构层：

- machine identity；
- communication set；
- machine program；
- protocol 的静态结构；
- caller / subroutine / subsidiary 关系。

这里先只刻画“协议长什么样”，而不在本文件里定义 UC 安全或组合定理。
-/

universe u v w

namespace LeanCryptoProtocols.UC

/-- machine identity。这里直接使用自然数，不在 identity 本身编码调用层级。 -/
abbrev MachineId : Type := Nat

/-- 环境的固定身份。 -/
def env_id : MachineId := 0

/-- 敌手的固定身份。 -/
def adv_id : MachineId := 1

/-- communication set 中的标准消息类型标签。 -/
inductive PortLabel where
  | input
  | subroutineOutput
  | backdoor
  deriving Repr, DecidableEq, Inhabited

/-- core 层用于区分普通/control 消息与静态腐化指令。 -/
inductive MessageInstruction where
  | plain
  | corrupt (party_id : MachineId)
  | dummyCaller (caller_id : MachineId)
  | dummyDestination (dest_id : MachineId)
  deriving Repr, DecidableEq, Inhabited

/-- 一个端口由发送者 identity、接收者 identity 和标签组成。 -/
structure CommPort where
  owner : MachineId
  dest : MachineId
  label : PortLabel
  well_formed :
    owner ≠ dest ∧
      (label = .backdoor ↔ (owner = adv_id ∨ dest = adv_id))
  deriving Repr, DecidableEq

/-- 机器发送的消息内容。 -/
structure Message (Payload : Type u) where
  /--
  Controller 认证后的发送方 identity。

  machine 构造 outgoing message 时通常保持默认值 `none`；controller 在投递前会
  按当前激活 machine 覆盖该字段。唯一例外是 environment 调用 main machine 时，
  environment 需要在这里提供对应的 external identity。
  -/
  source : Option MachineId := none
  label : PortLabel
  instruction : MessageInstruction := .plain
  payload : Payload
  instruction_valid :
    (∀ pid, instruction = .corrupt pid → label = .backdoor) ∧
      (∀ caller_id, instruction = .dummyCaller caller_id → label = .input) ∧
      (∀ dest_id, instruction = .dummyDestination dest_id → label = .subroutineOutput) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro id h <;> cases h
  deriving Repr, DecidableEq

namespace Message

/-- 腐化指令只能出现在 backdoor 消息上。 -/
theorem corrupt_instruction_implies_backdoor {Payload : Type u}
    (msg : Message Payload) {pid : MachineId} :
    msg.instruction = .corrupt pid → msg.label = .backdoor :=
  msg.instruction_valid.1 pid

/-- Dummy caller 指令只能出现在 input 消息上。 -/
theorem dummy_caller_instruction_implies_input {Payload : Type u}
    (msg : Message Payload) {caller_id : MachineId} :
    msg.instruction = .dummyCaller caller_id → msg.label = .input :=
  msg.instruction_valid.2.1 caller_id

/-- Dummy destination 指令只能出现在 subroutine-output 消息上。 -/
theorem dummy_destination_instruction_implies_subroutine_output {Payload : Type u}
    (msg : Message Payload) {dest_id : MachineId} :
    msg.instruction = .dummyDestination dest_id → msg.label = .subroutineOutput :=
  msg.instruction_valid.2.2 dest_id

end Message

/-- 发送给某个端口的一条消息。 -/
structure Envelope (Payload : Type u) where
  port : CommPort
  message : Message Payload
  label_matches : port.label = message.label
  deriving Repr, DecidableEq

/-- 一次原子 activation 的结果：更新状态，并至多发送一条消息。 -/
structure ActivationResult (Payload : Type u) (State : Type v) where
  state : State
  outgoing? : Option (Envelope Payload)
  deriving Repr, DecidableEq

/--
machine 的局部程序。

这里把局部状态类型封装在程序对象里；协议建模者需要写的是：

- 初始状态；
- 在当前状态下收到可选消息后，如何运行到“发送一条消息或挂起”为止；
- 是否已经 halt；
- 局部输出提取函数；
-/
structure MachineProgram (Payload : Type u) (Out : Type v) where
  LocalState : Type w
  init : ℕ → LocalState
  activate : LocalState → Option (Message Payload) → PMF (ActivationResult Payload LocalState)
  is_halted : LocalState → Bool
  output : LocalState → Out

/-- 一个 machine 由身份、communication set 和局部程序组成。 -/
structure Machine (Payload : Type u) (Out : Type v) where
  id : MachineId
  communication_set : Finset CommPort
  program : MachineProgram Payload Out
  well_formed :
    (∀ p ∈ communication_set, p.owner = id) ∧
      (∀ p₁ ∈ communication_set, ∀ p₂ ∈ communication_set, p₁.dest = p₂.dest → p₁ = p₂)

/-- 抹去输出类型后的 machine。 -/
abbrev AnyMachine (Payload : Type u) := Σ Out : Type, Machine Payload Out

/-- 抹去输出类型后的 machine 运行时初始状态。 -/
abbrev AnyMachineState (Payload : Type u) :=
  Σ m : AnyMachine Payload, m.2.program.LocalState

/-- 从异质 machine 中抽取 identity。 -/
def AnyMachine.id {Payload : Type u} (m : AnyMachine Payload) : MachineId :=
  m.2.id

/-- 抽取 protocol 中所有 machine identity。 -/
def machine_ids {Payload : Type u} (machines : List (AnyMachine Payload)) : List MachineId :=
  machines.map AnyMachine.id

/-- 按 machine 自身的 `init` 字段构造默认初始状态。 -/
def default_machine_states {Payload : Type u}
    (machines : List (AnyMachine Payload)) (n : ℕ) :
    List (AnyMachineState Payload) :=
  machines.map fun m => ⟨m, m.2.program.init n⟩

/-- 构造一个普通 `input` 端口。 -/
def mk_input_port (owner dest : MachineId) (hne : owner ≠ dest)
    (h_owner : owner ≠ adv_id) (h_dest : dest ≠ adv_id) : CommPort where
  owner := owner
  dest := dest
  label := .input
  well_formed := by
    refine ⟨hne, ?_⟩
    simp [h_owner, h_dest]

/-- 构造一个普通 `subroutine-output` 端口。 -/
def mk_subroutine_output_port (owner dest : MachineId) (hne : owner ≠ dest)
    (h_owner : owner ≠ adv_id) (h_dest : dest ≠ adv_id) : CommPort where
  owner := owner
  dest := dest
  label := .subroutineOutput
  well_formed := by
    refine ⟨hne, ?_⟩
    simp [h_owner, h_dest]

/-- 构造一个 `backdoor` 端口；control/corruption 语义由消息指令区分。 -/
def mk_backdoor_port (owner dest : MachineId)
    (hne : owner ≠ dest) (hadv : owner = adv_id ∨ dest = adv_id) : CommPort where
  owner := owner
  dest := dest
  label := .backdoor
  well_formed := by
    refine ⟨hne, ?_⟩
    simp [hadv]

/-- machine 是否允许向某个 identity 发送 `input` 消息。 -/
def can_send_input_to {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (mid : MachineId) : Prop :=
  ∃ p ∈ μ.communication_set, p.dest = mid ∧ p.label = .input

/-- machine 是否允许向某个 identity 发送 `subroutine-output` 消息。 -/
def can_send_subroutine_output_to {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (mid : MachineId) : Prop :=
  ∃ p ∈ μ.communication_set, p.dest = mid ∧ p.label = .subroutineOutput

/-- machine 是否允许向某个 identity 发送 `backdoor` 消息。 -/
def can_send_backdoor_to {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (mid : MachineId) : Prop :=
  ∃ p ∈ μ.communication_set, p.dest = mid ∧ p.label = .backdoor

/-- 若 `μ` 能向 `id` 发送 `input` 消息，则称 `μ` 是 `id` 的 caller。 -/
def is_caller_of_id {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (mid : MachineId) : Prop :=
  can_send_input_to μ mid

/-- 若 `μ` 能向 `id` 发送 `subroutine-output` 消息，则称 `μ` 是 `id` 的 subroutine。 -/
def is_subroutine_of_id {Payload : Type u} {Out : Type v}
    (μ : Machine Payload Out) (mid : MachineId) : Prop :=
  can_send_subroutine_output_to μ mid

/--
protocol 的静态外形。
本项目在这一层只记录 Section 2 里对 protocol 静态结构必需的约束；
真正的执行分布在 `Security.lean` 中经由 controller 给出。
-/
structure Protocol (Payload : Type u) where
  machines : List (AnyMachine Payload)
  initial_states : ℕ → PMF (List (AnyMachineState Payload)) :=
    fun n => PMF.pure (default_machine_states machines n)
  unique_ids : (machine_ids machines).Nodup
  caller_has_matching_subroutine :
    ∀ m ∈ machines, ∀ mid : MachineId,
      is_caller_of_id m.2 mid →
        ∃ m' ∈ machines, AnyMachine.id m' = mid ∧ is_subroutine_of_id m'.2 (AnyMachine.id m)
  subroutine_has_matching_caller :
    ∀ m ∈ machines, ∀ mid : MachineId,
      is_subroutine_of_id m.2 mid →
        mid ∈ machine_ids machines →
        ∃ m' ∈ machines, AnyMachine.id m' = mid ∧ is_caller_of_id m'.2 (AnyMachine.id m)
  env_separated : env_id ∉ machine_ids machines
  adv_separated : adv_id ∉ machine_ids machines
  no_direct_environment_communication :
    ∀ m ∈ machines, ∀ p ∈ m.2.communication_set, p.dest ≠ env_id

/-- protocol 中是否存在某个给定 identity 的 machine。 -/
def Protocol.has_machine_id {Payload : Type u}
    (π : Protocol Payload) (mid : MachineId) : Prop :=
  mid ∈ machine_ids π.machines

/-- 查找某个 identity 对应的 machine。 -/
def Protocol.machine_by_id? {Payload : Type u}
    (π : Protocol Payload) (mid : MachineId) : Option (AnyMachine Payload) :=
  π.machines.find? (fun m => AnyMachine.id m = mid)

/-- protocol 中 `parent` 是否拥有一个 id 为 `child` 的直接 subroutine。 -/
def Protocol.machine_is_subroutine_of {Payload : Type u}
    (π : Protocol Payload) (child parent : MachineId) : Prop :=
  ∃ m_child ∈ π.machines, ∃ m_parent ∈ π.machines,
    AnyMachine.id m_child = child ∧
      AnyMachine.id m_parent = parent ∧
      is_subroutine_of_id m_child.2 parent

/-- protocol 中 `parent` 是否是 id 为 `child` 的 machine 的直接 caller。 -/
def Protocol.machine_is_caller_of {Payload : Type u}
    (π : Protocol Payload) (parent child : MachineId) : Prop :=
  ∃ m_parent ∈ π.machines, ∃ m_child ∈ π.machines,
    AnyMachine.id m_parent = parent ∧
      AnyMachine.id m_child = child ∧
      is_caller_of_id m_parent.2 child

/-- subsidiary 关系：通过 subroutine 关系的传递闭包得到。 -/
def Protocol.machine_is_subsidiary_of {Payload : Type u}
    (π : Protocol Payload) (child parent : MachineId) : Prop :=
  Relation.TransGen (Protocol.machine_is_subroutine_of π) child parent

/--
`mid` 是 machine `μ` 相对于协议 `π` 的 external identity。

按 Canetti 第 2 节的表述，这意味着：

- `μ` 属于 `π`；
- `μ` 是 `mid` 的 subroutine；
- `mid` 不是 `π` 中任何 machine 的 identity。
-/
def Protocol.is_external_identity_of {Payload : Type u}
    (π : Protocol Payload) (μ : AnyMachine Payload) (mid : MachineId) : Prop :=
  μ ∈ π.machines ∧
    is_subroutine_of_id μ.2 mid ∧
    mid ∉ machine_ids π.machines

/-- `mid` 是否是 `π` 的 main machine。 -/
def Protocol.is_main_machine {Payload : Type u}
    (π : Protocol Payload) (mid : MachineId) : Prop :=
  ∃ μ ∈ π.machines, AnyMachine.id μ = mid ∧
    ∃ ext_id, π.is_external_identity_of μ ext_id

/-- `mid` 是否是 `π` 的 internal machine。 -/
def Protocol.is_internal_machine {Payload : Type u}
    (π : Protocol Payload) (mid : MachineId) : Prop :=
  π.has_machine_id mid ∧ ¬ π.is_main_machine mid

/-- 某个 main machine 相对于协议的 external identities。 -/
def Protocol.external_identities_of {Payload : Type u}
    (π : Protocol Payload) (mid : MachineId) : Set MachineId :=
  { ext_id | ∃ μ ∈ π.machines, AnyMachine.id μ = mid ∧ π.is_external_identity_of μ ext_id }

/-- 所有 main machine identities 的集合。 -/
noncomputable def Protocol.main_machine_ids {Payload : Type u}
    (π : Protocol Payload) : Finset MachineId :=
  by
    classical
    exact (machine_ids π.machines).toFinset.filter π.is_main_machine

/-- 所有 internal machine identities 的集合。 -/
noncomputable def Protocol.internal_machine_ids {Payload : Type u}
    (π : Protocol Payload) : Finset MachineId :=
  by
    classical
    exact (machine_ids π.machines).toFinset.filter π.is_internal_machine

@[simp] theorem env_id_eq_zero : env_id = 0 := rfl

@[simp] theorem adv_id_eq_one : adv_id = 1 := rfl

end LeanCryptoProtocols.UC

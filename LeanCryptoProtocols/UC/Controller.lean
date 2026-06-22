import LeanCryptoProtocols.Config
import LeanCryptoProtocols.UC.Machine
import LeanCryptoProtocols.UC.Indistinguishability

/-!
# Controller 与执行安装

本文件收纳所有依赖
`protocol + adversary + environment` 三者才能判断的执行期对象：

- environment；
- adversary / simulator；
- execution setup；
- 运行时 backdoor overlay；
- controller 的运行状态与逐步调度；
- controller 诱导出的输出 ensemble。

这里使用一个有界的 controller 执行器：
`exec n` 中的 `n` 只作为安全参数索引；
controller 的步数预算由 `LeanCryptoProtocols.max_controller_steps` 给出。
-/

universe u v

namespace LeanCryptoProtocols.UC

/-- 环境本身也是一个 machine。 -/
structure Environment (Payload : Type u) where
  machine : Machine Payload Bool
  id_matches : machine.id = env_id
  unique_backdoor_port_to_adversary :
    ∃! p, p ∈ machine.communication_set ∧ p.dest = adv_id ∧ p.label = .backdoor

/-- 敌手本身也是一个 machine；静态腐化集合由 `ExecutionSetup` 固定。 -/
structure Adversary (Payload : Type u) where
  machine : Machine Payload Unit
  id_matches : machine.id = adv_id
  unique_backdoor_port_to_environment :
    ∃! p, p ∈ machine.communication_set ∧ p.dest = env_id ∧ p.label = .backdoor

/-- 在理想世界里，simulator 扮演 adversary 的角色。 -/
abbrev Simulator (Payload : Type u) := Adversary Payload

/--
对给定 `protocol + adversary + environment` 的一次经过审计的执行安装。

所有依赖三者同时出现才能判断真伪的约束，都集中放在这里。
-/
structure ExecutionSetup {Payload : Type u}
    (protocol : Protocol Payload)
    (adversary : Adversary Payload)
    (environment : Environment Payload) where
  /-- 本次执行固定的 static corruption pattern。 -/
  corrupted_parties : Finset MachineId
  env_port_policy_holds :
    ∀ p ∈ environment.machine.communication_set,
      (p.dest = adv_id ∧ p.label = .backdoor) ∨
        (p.dest ≠ adv_id ∧ p.label = .input ∧ protocol.is_main_machine p.dest)
  corruption_allowed :
    corrupted_parties ⊆ protocol.corruptible_machines
  adv_port_destinations_restricted :
    ∀ p ∈ adversary.machine.communication_set,
      p.dest = env_id

namespace ExecutionSetup

/-- protocol 内某个 identity 对应的基础 communication set。 -/
def protocol_comm_set {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Finset CommPort :=
  match π.machine_by_id? mid with
  | some m => m.2.communication_set
  | none => ∅

/-- protocol machine 到 adversary 的运行时 backdoor 端口。 -/
def backdoor_port_to_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Option CommPort :=
  if h_mem : mid ∈ machine_ids π.machines then
    some <|
      mk_backdoor_port mid adv_id
        (by
          intro h_eq
          exact π.adv_separated (by simpa [h_eq] using h_mem))
        (Or.inr rfl)
  else
    none

/-- adversary 到 protocol machine 的运行时 backdoor 端口。 -/
def backdoor_port_from_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Option CommPort :=
  if h_mem : mid ∈ machine_ids π.machines then
    some <|
      mk_backdoor_port adv_id mid
        (by
          intro h_eq
          exact π.adv_separated (by simpa [← h_eq] using h_mem))
        (Or.inl rfl)
  else
    none

/-- 环境到 protocol 内 main machine 的输入端口。 -/
noncomputable def env_input_port_to_main {Payload : Type u} (π : Protocol Payload)
    (mid : MachineId) : Option CommPort :=
  by
  classical
  if h_main : mid ∈ π.main_machine_ids then
    let h_mid_machine : mid ∈ machine_ids π.machines :=
      List.mem_toFinset.mp (Finset.mem_filter.mp h_main).1
    exact
      some <|
        mk_input_port env_id mid
          (by
            intro h_eq
            subst h_eq
            exact π.env_separated h_mid_machine)
          (by simp [env_id, adv_id])
          (by
            intro h_eq
            subst h_eq
            exact π.adv_separated h_mid_machine)
  else
    exact none

/-- 某个发送者在运行时可见的 communication set。 -/
noncomputable def runtime_communication_set {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (sender_id : MachineId) : Finset CommPort :=
  let env_input_ports : Finset CommPort :=
    by
      classical
      exact (π.main_machine_ids.toList.filterMap fun mid => env_input_port_to_main π mid).toFinset
  if _h_env : sender_id = env_id then
    E.machine.communication_set ∪ env_input_ports
  else if _h_adv : sender_id = adv_id then
    let base := A.machine.communication_set
    let backdoor_ports :=
      (machine_ids π.machines).filterMap fun mid =>
        setup.backdoor_port_from_adversary mid
    base ∪ backdoor_ports.toFinset
  else
    let base := setup.protocol_comm_set sender_id
    match setup.backdoor_port_to_adversary sender_id with
    | some p => insert p base
    | none => base

/-- 消息是否发往系统中已有的某个 machine。 -/
def routes_to_system_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Prop :=
  mid = env_id ∨ mid = adv_id ∨ π.has_machine_id mid

/-- 消息是否发往协议的某个 external identity。 -/
def routes_to_external_identity {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Prop :=
  ∃ μ ∈ π.machines, π.is_external_identity_of μ mid

/-- 环境发出的消息是否满足 source identity 约束。 -/
def environment_source_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (envelope : Envelope Payload) : Prop :=
  if _h_adv : envelope.port.dest = adv_id then
    envelope.message.source = none
  else
    ∃ ext_id,
      envelope.message.source = some ext_id ∧
        ext_id ∈ π.external_identities_of envelope.port.dest

/-- 非环境发送者发出的消息是否满足 source identity 约束。 -/
def sender_source_valid {Payload : Type u}
    (sender_id : MachineId) (envelope : Envelope Payload) : Prop :=
  envelope.message.source = some sender_id

/-- core 层检查腐化指令是否越过固定 static corruption set。 -/
def corruption_instruction_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (envelope : Envelope Payload) : Prop :=
  match envelope.message.instruction with
  | .plain => True
  | .corrupt pid =>
      envelope.message.label = .backdoor ∧ pid ∈ _setup.corrupted_parties

/-- 当前发送者发出的消息是否满足 controller 的运行时检查。 -/
def outgoing_message_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (sender_id : MachineId) (envelope : Envelope Payload) : Prop :=
  envelope.port.owner = sender_id ∧
    envelope.port ∈ setup.runtime_communication_set sender_id ∧
    setup.corruption_instruction_valid envelope ∧
    (if _h_env : sender_id = env_id then
      setup.environment_source_valid envelope
    else
      sender_source_valid sender_id envelope)

end ExecutionSetup

/-- 运行时的一个 protocol machine 局部状态。 -/
structure ProtocolMachineState (Payload : Type u) where
  Out : Type
  machine : Machine Payload Out
  state : machine.program.LocalState

namespace ProtocolMachineState

/-- 从异质 machine 初始化运行时状态。 -/
def of_any_machine {Payload : Type u}
    (m : AnyMachine Payload) (n : ℕ) : ProtocolMachineState Payload :=
  { Out := m.1
    machine := m.2
    state := m.2.program.init n }

/-- 从 protocol 提供的异质 machine state 初始化运行时状态。 -/
def of_any_machine_state {Payload : Type u}
    (st : AnyMachineState Payload) : ProtocolMachineState Payload :=
  { Out := st.1.1
    machine := st.1.2
    state := st.2 }

/-- 运行时状态对应的 machine identity。 -/
def id {Payload : Type u} (st : ProtocolMachineState Payload) : MachineId :=
  st.machine.id

/-- 向该 machine 投递一条消息。 -/
def receive {Payload : Type u}
    (st : ProtocolMachineState Payload) (msg : Message Payload) :
    ProtocolMachineState Payload :=
  { st with state := st.machine.program.receive st.state msg }

/-- 让该 machine 恢复执行一次。 -/
noncomputable def resume {Payload : Type u}
    (st : ProtocolMachineState Payload) :
    PMF (ProtocolMachineState Payload × Option (Envelope Payload)) :=
  (st.machine.program.resume st.state).bind fun result =>
    PMF.pure
      ({ Out := st.Out, machine := st.machine, state := result.state },
        result.outgoing?)

end ProtocolMachineState

/--
controller 的运行时状态。

环境和敌手的局部状态单独保存；
协议内部各 machine 的局部状态以列表保存。
-/
structure ControllerState {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) where
  env_state : E.machine.program.LocalState
  adv_state : A.machine.program.LocalState
  protocol_states : List (ProtocolMachineState Payload)
  active_id : MachineId

namespace Controller

/-- Controller 结束原因。 -/
inductive ExitStatus where
  | halted
  | budget_exceeded
  deriving Repr, DecidableEq

/-- 初始 controller 状态：所有 machine 都处于初始局部状态，先激活环境。 -/
def initial_state {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (n : ℕ) : ControllerState setup where
  env_state := E.machine.program.init n
  adv_state := A.machine.program.init n
  protocol_states := π.machines.map (fun m => ProtocolMachineState.of_any_machine m n)
  active_id := env_id

/-- 使用 protocol 提供的初始 machine states 构造 controller 状态。 -/
def initial_state_with_protocol_states {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (n : ℕ)
    (protocol_states : List (AnyMachineState Payload)) : ControllerState setup where
  env_state := E.machine.program.init n
  adv_state := A.machine.program.init n
  protocol_states := protocol_states.map ProtocolMachineState.of_any_machine_state
  active_id := env_id

/-- 查找某个 protocol machine 的当前运行时状态。 -/
def find_protocol_state? {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (mid : MachineId) :
    Option (ProtocolMachineState Payload) :=
  st.protocol_states.find? fun m => m.id = mid

/-- 用新的局部状态替换某个 protocol machine 的当前运行时状态。 -/
def replace_protocol_state {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (new_state : ProtocolMachineState Payload) :
    ControllerState setup :=
  { st with
    protocol_states := st.protocol_states.map fun m =>
      if m.id = new_state.id then new_state else m }

/-- 环境是否已经 halt。 -/
def environment_halted {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) : Bool :=
  E.machine.program.is_halted st.env_state

/-- 当前环境输出。 -/
def environment_output {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) : Bool :=
  E.machine.program.output st.env_state

/-- 向环境投递一条消息并激活环境。 -/
def deliver_to_environment {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (msg : Envelope Payload) :
    ControllerState setup :=
  { st with
    env_state := E.machine.program.receive st.env_state msg.message
    active_id := env_id }

/-- 向 adversary 投递一条消息并激活 adversary。 -/
def deliver_to_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (msg : Envelope Payload) :
    ControllerState setup :=
  { st with
    adv_state := A.machine.program.receive st.adv_state msg.message
    active_id := adv_id }

/-- 向某个 protocol machine 投递一条消息并激活该 machine。 -/
def deliver_to_protocol_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (mid : MachineId) (msg : Envelope Payload) :
    ControllerState setup :=
  match find_protocol_state? st mid with
  | some target =>
      let target' := ProtocolMachineState.receive target msg.message
      { (replace_protocol_state st target') with active_id := mid }
  | none =>
      { st with active_id := env_id }

/-- 根据 envelope 的目的地路由消息。 -/
noncomputable def route_envelope {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId) (msg : Envelope Payload) :
    ControllerState setup := by
  classical
  if h_sys : setup.routes_to_system_machine msg.port.dest then
    if _h_env : msg.port.dest = env_id then
      exact deliver_to_environment st msg
    else if _h_adv : msg.port.dest = adv_id then
      exact deliver_to_adversary st msg
    else
      exact deliver_to_protocol_machine st msg.port.dest msg
  else if h_ext :
      sender_id ≠ env_id ∧
      setup.routes_to_external_identity msg.port.dest ∧
      msg.message.label = .subroutineOutput then
    exact deliver_to_environment st msg
  else
    exact { st with active_id := env_id }

/-- 处理某次恢复执行后的可选外发消息。 -/
noncomputable def handle_outgoing {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId)
    (outgoing? : Option (Envelope Payload)) : PMF (ControllerState setup) := by
  classical
  match outgoing? with
  | none =>
      exact PMF.pure { st with active_id := env_id }
  | some msg =>
      if h_valid : setup.outgoing_message_valid sender_id msg then
        exact PMF.pure (route_envelope setup st sender_id msg)
      else
        exact PMF.pure { st with active_id := env_id }

/-- If a machine pauses without an outgoing message, control returns to the environment. -/
theorem handle_outgoing_none {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId) :
    handle_outgoing setup st sender_id none =
      PMF.pure { st with active_id := env_id } := by
  simp [handle_outgoing]

/-- A valid outgoing envelope is routed by the controller. -/
theorem handle_outgoing_some_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId)
    (msg : Envelope Payload)
    (h_valid : setup.outgoing_message_valid sender_id msg) :
    handle_outgoing setup st sender_id (some msg) =
      PMF.pure (route_envelope setup st sender_id msg) := by
  simp [handle_outgoing, h_valid]

/-- An invalid outgoing envelope is dropped and control returns to the environment. -/
theorem handle_outgoing_some_invalid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId)
    (msg : Envelope Payload)
    (h_invalid : ¬ setup.outgoing_message_valid sender_id msg) :
    handle_outgoing setup st sender_id (some msg) =
      PMF.pure { st with active_id := env_id } := by
  simp [handle_outgoing, h_invalid]

/--
If an envelope is addressed to a protocol machine, routing delivers it to that
machine rather than to the environment or adversary.
-/
theorem route_envelope_to_protocol_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId)
    (msg : Envelope Payload)
    (h_system : setup.routes_to_system_machine msg.port.dest)
    (h_not_env : msg.port.dest ≠ env_id)
    (h_not_adv : msg.port.dest ≠ adv_id) :
    route_envelope setup st sender_id msg =
      deliver_to_protocol_machine st msg.port.dest msg := by
  have h_not_env_zero : msg.port.dest ≠ 0 := by
    simpa [env_id] using h_not_env
  have h_not_adv_one : msg.port.dest ≠ 1 := by
    simpa [adv_id] using h_not_adv
  simp [route_envelope, h_system, h_not_env_zero, h_not_adv_one]

/--
If a non-environment protocol machine sends a subroutine output to one of the
protocol's external identities, the controller delivers that message back to
the environment.
-/
theorem route_envelope_to_external_identity {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (sender_id : MachineId)
    (msg : Envelope Payload)
    (h_not_system : ¬ setup.routes_to_system_machine msg.port.dest)
    (h_sender : sender_id ≠ env_id)
    (h_external : setup.routes_to_external_identity msg.port.dest)
    (h_label : msg.message.label = .subroutineOutput) :
    route_envelope setup st sender_id msg =
      deliver_to_environment st msg := by
  have h_sender_zero : sender_id ≠ 0 := by
    simpa [env_id] using h_sender
  simp [route_envelope, h_not_system, h_sender_zero, h_external, h_label]

/--
If the destination protocol-machine state is present, delivery updates only
that local state and makes it active.
-/
theorem deliver_to_protocol_machine_of_find {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (mid : MachineId)
    (msg : Envelope Payload)
    (target : ProtocolMachineState Payload)
    (h_find : find_protocol_state? st mid = some target) :
    deliver_to_protocol_machine st mid msg =
      { (replace_protocol_state st (ProtocolMachineState.receive target msg.message)) with
        active_id := mid } := by
  simp [deliver_to_protocol_machine, h_find]

/-- 激活环境一次。 -/
noncomputable def step_environment {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) : PMF (ControllerState setup) :=
  (E.machine.program.resume st.env_state).bind fun result =>
    let st' : ControllerState setup :=
      { st with env_state := result.state }
    handle_outgoing setup st' env_id result.outgoing?

/-- 激活 adversary 一次。 -/
noncomputable def step_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) : PMF (ControllerState setup) :=
  (A.machine.program.resume st.adv_state).bind fun result =>
    let st' : ControllerState setup :=
      { st with adv_state := result.state }
    handle_outgoing setup st' adv_id result.outgoing?

/-- 如果环境的 `resume` 是纯结果，则环境单步就是对应的 `handle_outgoing`。 -/
theorem step_environment_of_resume {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup)
    (result : ActivationResult Payload E.machine.program.LocalState)
    (h_resume :
      E.machine.program.resume st.env_state = PMF.pure result) :
    step_environment setup st =
      handle_outgoing setup { st with env_state := result.state } env_id result.outgoing? := by
  simp [step_environment, h_resume]

/-- 如果 adversary 的 `resume` 是纯结果，则 adversary 单步就是对应的 `handle_outgoing`。 -/
theorem step_adversary_of_resume {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup)
    (result : ActivationResult Payload A.machine.program.LocalState)
    (h_resume :
      A.machine.program.resume st.adv_state = PMF.pure result) :
    step_adversary setup st =
      handle_outgoing setup { st with adv_state := result.state } adv_id result.outgoing? := by
  simp [step_adversary, h_resume]

/-- 激活某个 protocol machine 一次。 -/
noncomputable def step_protocol_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (mid : MachineId) : PMF (ControllerState setup) :=
  match find_protocol_state? st mid with
  | none =>
      PMF.pure { st with active_id := env_id }
  | some machine_state =>
      (ProtocolMachineState.resume machine_state).bind fun result =>
        let st' := replace_protocol_state st result.1
        handle_outgoing setup st' mid result.2

/--
If the active protocol machine is found and its local resume distribution is a
pure result, one controller protocol step is exactly the corresponding
`handle_outgoing` call.
-/
theorem step_protocol_machine_of_find_resume {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (mid : MachineId)
    (machine_state new_state : ProtocolMachineState Payload)
    (outgoing? : Option (Envelope Payload))
    (h_find : find_protocol_state? st mid = some machine_state)
    (h_resume :
      ProtocolMachineState.resume machine_state =
        PMF.pure (new_state, outgoing?)) :
    step_protocol_machine setup st mid =
      handle_outgoing setup (replace_protocol_state st new_state) mid outgoing? := by
  simp [step_protocol_machine, h_find, h_resume]

/--
Specialized form of `step_protocol_machine_of_find_resume` for the common case
where the resumed machine emits a valid envelope.
-/
theorem step_protocol_machine_of_find_resume_some_valid
    {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (mid : MachineId)
    (machine_state new_state : ProtocolMachineState Payload)
    (msg : Envelope Payload)
    (h_find : find_protocol_state? st mid = some machine_state)
    (h_resume :
      ProtocolMachineState.resume machine_state =
        PMF.pure (new_state, some msg))
    (h_valid : setup.outgoing_message_valid mid msg) :
    step_protocol_machine setup st mid =
      PMF.pure (route_envelope setup (replace_protocol_state st new_state) mid msg) := by
  rw [step_protocol_machine_of_find_resume setup st mid machine_state new_state (some msg)
    h_find h_resume]
  exact handle_outgoing_some_valid setup (replace_protocol_state st new_state) mid msg h_valid

/--
Specialized form of `step_protocol_machine_of_find_resume` for a pause without
an outgoing envelope.
-/
theorem step_protocol_machine_of_find_resume_none {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (mid : MachineId)
    (machine_state new_state : ProtocolMachineState Payload)
    (h_find : find_protocol_state? st mid = some machine_state)
    (h_resume :
      ProtocolMachineState.resume machine_state =
        PMF.pure (new_state, none)) :
    step_protocol_machine setup st mid =
      PMF.pure { (replace_protocol_state st new_state) with active_id := env_id } := by
  rw [step_protocol_machine_of_find_resume setup st mid machine_state new_state none
    h_find h_resume]
  exact handle_outgoing_none setup (replace_protocol_state st new_state) mid

/-- controller 的单步调度。 -/
noncomputable def step {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) : PMF (ControllerState setup) :=
  if environment_halted st then
    PMF.pure st
  else if _h_env : st.active_id = env_id then
    step_environment setup st
  else if _h_adv : st.active_id = adv_id then
    step_adversary setup st
  else
    step_protocol_machine setup st st.active_id

/-- 当前 active machine 是环境时，`step` 展开为 `step_environment`。 -/
theorem step_of_environment {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup)
    (h_halted : environment_halted st = false)
    (h_active : st.active_id = env_id) :
    step setup st = step_environment setup st := by
  simp [step, h_halted, h_active]

/-- 当前 active machine 是 adversary 时，`step` 展开为 `step_adversary`。 -/
theorem step_of_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup)
    (h_halted : environment_halted st = false)
    (h_active : st.active_id = adv_id) :
    step setup st = step_adversary setup st := by
  simp [step, h_halted, h_active]

/-- 当前 active machine 是普通 protocol machine 时，`step` 展开为 `step_protocol_machine`。 -/
theorem step_of_protocol_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup)
    (h_halted : environment_halted st = false)
    (h_not_env : st.active_id ≠ env_id)
    (h_not_adv : st.active_id ≠ adv_id) :
    step setup st = step_protocol_machine setup st st.active_id := by
  have h_not_env_zero : st.active_id ≠ 0 := by
    simpa [env_id] using h_not_env
  have h_not_adv_one : st.active_id ≠ 1 := by
    simpa [adv_id] using h_not_adv
  simp [step, h_halted, h_not_env_zero, h_not_adv_one]

/--
在步数预算 `fuel` 内运行 controller。

若环境提早 halt，则立即停止；否则在预算耗尽时返回当前环境状态。
-/
noncomputable def run_steps {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) :
    Nat → ControllerState setup → PMF (ControllerState setup)
  | 0, st => PMF.pure st
  | fuel + 1, st =>
      if environment_halted st then
        PMF.pure st
      else
        (step setup st).bind fun st' => run_steps setup fuel st'

/--
Controller 的函数式模拟引理。

如果 `map_state` 保持环境 halt 判断，并且一次 controller step 与 `map_state`
交换，那么任意步数预算下的 `run_steps` 也与 `map_state` 交换。DHKE 等具体
证明可以把真实执行状态投影到 challenge/ideal 执行状态，再用该引理把局部
machine step 等式提升为完整 controller trace 等式。
-/
theorem run_steps_map_of_step_map {Payload : Type u}
    {π₁ π₂ : Protocol Payload}
    {A₁ A₂ : Adversary Payload}
    {E₁ E₂ : Environment Payload}
    {setup₁ : ExecutionSetup π₁ A₁ E₁}
    {setup₂ : ExecutionSetup π₂ A₂ E₂}
    (map_state : ControllerState setup₁ → ControllerState setup₂)
    (h_halted :
      ∀ st, environment_halted (map_state st) = environment_halted st)
    (h_step :
      ∀ st, environment_halted st = false →
        step setup₂ (map_state st) =
          (step setup₁ st).bind fun st' => PMF.pure (map_state st')) :
    ∀ fuel st,
      run_steps setup₂ fuel (map_state st) =
        (run_steps setup₁ fuel st).bind fun st' => PMF.pure (map_state st') := by
  intro fuel
  induction fuel with
  | zero =>
      intro st
      simp [run_steps]
  | succ fuel ih =>
      intro st
      by_cases h : environment_halted st = true
      · have h₂ : environment_halted (map_state st) = true := by
          simp [h_halted st, h]
        simp [run_steps, h, h₂]
      · have h_false : environment_halted st = false := by
          cases hst : environment_halted st <;> simp [hst] at h ⊢
        have h₂_false : environment_halted (map_state st) = false := by
          simp [h_halted st, h_false]
        simp [run_steps, h_false, h₂_false, h_step st h_false, PMF.bind_bind, ih]

/--
`run_steps_map_of_step_map` 的输出分布版本。

除了 step-level 交换外，如果 `map_state` 还保持环境输出，则两个 controller
run 在输出层完全相同。
-/
theorem run_steps_output_eq_of_step_map {Payload : Type u}
    {π₁ π₂ : Protocol Payload}
    {A₁ A₂ : Adversary Payload}
    {E₁ E₂ : Environment Payload}
    {setup₁ : ExecutionSetup π₁ A₁ E₁}
    {setup₂ : ExecutionSetup π₂ A₂ E₂}
    (map_state : ControllerState setup₁ → ControllerState setup₂)
    (h_halted :
      ∀ st, environment_halted (map_state st) = environment_halted st)
    (h_output :
      ∀ st, environment_output (map_state st) = environment_output st)
    (h_step :
      ∀ st, environment_halted st = false →
        step setup₂ (map_state st) =
          (step setup₁ st).bind fun st' => PMF.pure (map_state st'))
    (fuel : Nat) (st : ControllerState setup₁) :
    (run_steps setup₂ fuel (map_state st)).bind
        (fun st₂ => PMF.pure (environment_output st₂)) =
      (run_steps setup₁ fuel st).bind
        (fun st₁ => PMF.pure (environment_output st₁)) := by
  rw [run_steps_map_of_step_map map_state h_halted h_step fuel st]
  simp [PMF.bind_bind, h_output]

/--
在步数预算内运行 controller，并记录是正常 halt 还是耗尽预算。

若初始状态或某次调度后环境 halt，返回 `.halted`；
若 fuel 用尽且环境仍未 halt，返回 `.budget_exceeded`。
-/
noncomputable def run_steps_with_status {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) :
    Nat → ControllerState setup → PMF (ControllerState setup × ExitStatus)
  | 0, st =>
      PMF.pure
        (st, if environment_halted st then ExitStatus.halted else ExitStatus.budget_exceeded)
  | fuel + 1, st =>
      if environment_halted st then
        PMF.pure (st, ExitStatus.halted)
      else
        (step setup st).bind fun st' => run_steps_with_status setup fuel st'

/--
`exec n` 是当前 uniform 模型下的 controller 输出 ensemble。

`n` 只是安全参数索引；
TODO: 未来还需要在合适的地方记录n，用于 reduction
controller 不用它限制 machine 的多项式运行时间。
实际执行预算使用项目配置中的大常数 `max_controller_steps`。
-/
noncomputable def exec {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) : Ensemble Bool :=
  fun n =>
    (π.initial_states n).bind fun protocol_states =>
      (run_steps setup LeanCryptoProtocols.max_controller_steps
          (initial_state_with_protocol_states setup n protocol_states)).bind fun st =>
        PMF.pure (environment_output st)

/-- Controller 输出及退出原因。用于可执行 harness 检查预算耗尽。 -/
noncomputable def exec_with_status {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) : Ensemble (Bool × ExitStatus) :=
  fun n =>
    (π.initial_states n).bind fun protocol_states =>
      (run_steps_with_status setup LeanCryptoProtocols.max_controller_steps
          (initial_state_with_protocol_states setup n protocol_states)).bind fun result =>
        PMF.pure (environment_output result.1, result.2)

/-- Controller 预算耗尽时给命令行 wrapper 使用的提示。 -/
def budget_exceeded_warning : String :=
  "warning: UC controller exceeded max_controller_steps before the environment halted"

/--
命令行 wrapper 的最小提醒接口。

纯 `Controller.exec` 不能产生 IO 副作用；实际 runner 应在得到 `.budget_exceeded`
时调用这个函数打印提醒。
-/
def warn_if_budget_exceeded : ExitStatus → IO Unit
  | .halted => pure ()
  | .budget_exceeded => IO.eprintln budget_exceeded_warning

/--
Controller 执行保持 PPT 的通用闭包接口。

若 adversary 与 environment 是 PPT，并且 reduction 只是在每个挑战样本下
构造一个完整的 controller setup 后运行 controller，那么得到的 uniform
distinguisher 仍是 PPT。该接口只记录复杂度闭包，不断言任何执行等价、
概率界或密码学安全结论。
-/
axiom ppt_controller_distinguisher
    {α : Type v} {Payload : Type u}
    {π : α → Protocol Payload}
    {A : Adversary Payload}
    {E : Environment Payload}
    (setup : ∀ x, ExecutionSetup (π x) A E) :
    PPT A → PPT E →
      PPT ({ run := fun x n => Controller.exec (setup x) n } : Distinguisher α)

end Controller

end LeanCryptoProtocols.UC

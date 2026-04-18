import LeanCryptoProtocols.UC.Machine
import LeanCryptoProtocols.UC.Indistinguishability

/-!
# Controller 与执行安装

本文件收纳所有依赖 `protocol + adversary + environment` 三者才能判断的执行期对象：

- environment；
- adversary / simulator；
- execution setup；
- 运行时 backdoor overlay；
- controller 的运行状态与逐步调度；
- controller 诱导出的输出 ensemble。

这里使用一个有界的 controller 执行器：`exec n` 在安全参数 `n` 给出的预算内
反复调度，若环境提早 halt，则立即输出环境结果。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- 环境本身也是一个 machine。 -/
structure Environment (Payload : Type u) where
  machine : Machine Payload Bool
  id_matches : machine.id = env_id
  unique_backdoor_port_to_adversary :
    ∃! p, p ∈ machine.communication_set ∧ p.dest = adv_id ∧ p.label = .backdoor

/--
半诚实、静态腐化敌手。

这里不提供主动篡改 honest machine 程序的接口；敌手只携带一个 adversary machine
和一个初始静态腐化集合。
-/
structure Adversary (Payload : Type u) where
  machine : Machine Payload Unit
  corruption_set : Finset MachineId
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
  env_port_policy_holds :
    ∀ p ∈ environment.machine.communication_set,
      (p.dest = adv_id ∧ p.label = .backdoor) ∨
        (p.dest ≠ adv_id ∧ p.label = .input ∧ protocol.is_main_machine p.dest)
  adv_corruption_within_protocol :
    adversary.corruption_set ⊆ (machine_ids protocol.machines).toFinset
  adv_port_destinations_restricted :
    ∀ p ∈ adversary.machine.communication_set,
      p.dest ∈ adversary.corruption_set ∪ {env_id}

namespace ExecutionSetup

/-- protocol 内某个 identity 对应的基础 communication set。 -/
def protocol_comm_set {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Finset CommPort :=
  match π.machine_by_id? mid with
  | some m => m.2.communication_set
  | none => ∅

/-- 若 `mid` 被腐化，则它到 adversary 的运行时 backdoor 端口。 -/
def backdoor_port_to_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Option CommPort :=
  if _h_mem : mid ∈ A.corruption_set then
    if h_ne : mid ≠ adv_id then
      some (mk_backdoor_port mid adv_id h_ne (Or.inr rfl))
    else
      none
  else
    none

/-- adversary 到某个被腐化 machine 的运行时 backdoor 端口。 -/
def backdoor_port_from_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (mid : MachineId) : Option CommPort :=
  if _h_mem : mid ∈ A.corruption_set then
    if h_ne : adv_id ≠ mid then
      some (mk_backdoor_port adv_id mid h_ne (Or.inl rfl))
    else
      none
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
    let extra :=
      A.corruption_set.toList.filterMap fun mid =>
        setup.backdoor_port_from_adversary mid
    base ∪ extra.toFinset
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

/-- 当前发送者发出的消息是否满足 controller 的运行时检查。 -/
def outgoing_message_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (sender_id : MachineId) (envelope : Envelope Payload) : Prop :=
  envelope.port.owner = sender_id ∧
    envelope.port ∈ setup.runtime_communication_set sender_id ∧
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
    (m : AnyMachine Payload) : ProtocolMachineState Payload :=
  { Out := m.1
    machine := m.2
    state := m.2.program.init }

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
      ({ Out := st.Out, machine := st.machine, state := result.state }, result.outgoing?)

end ProtocolMachineState

/--
controller 的运行时状态。

环境和敌手的局部状态单独保存；协议内部各 machine 的局部状态以列表保存。
-/
structure ControllerState {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) where
  env_state : E.machine.program.LocalState
  adv_state : A.machine.program.LocalState
  protocol_states : List (ProtocolMachineState Payload)
  active_id : MachineId

namespace Controller

/-- 初始 controller 状态：所有 machine 都处于初始局部状态，先激活环境。 -/
def initial_state {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) : ControllerState setup where
  env_state := E.machine.program.init
  adv_state := A.machine.program.init
  protocol_states := π.machines.map ProtocolMachineState.of_any_machine
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
`exec n` 是当前 uniform 模型下的 controller 输出 ensemble。

这里使用安全参数 `n` 作为执行预算：controller 最多调度 `n` 次恢复执行，
如果环境在此之前 halt，则返回最终输出。
-/
noncomputable def exec {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) : Ensemble Bool :=
  fun n => -- TODO: 这里的 n 是安全参数还是步数预算？如果是安全参数的话，controller 的执行预算应该是某个函数 f(n) 吧？或者干脆直接用步数预算，不用安全参数了？
    (run_steps setup n (initial_state setup)).bind fun st =>
      PMF.pure (environment_output st)

end Controller

end LeanCryptoProtocols.UC

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
  communication_set_is_singleton_backdoor_to_adversary :
    ∃ p, machine.communication_set = {p} ∧
      p.dest = adv_id ∧ p.label = .backdoor

/-- 敌手本身也是一个 machine；静态腐化集合由 `ExecutionSetup` 固定。 -/
structure Adversary (Payload : Type u) where
  machine : Machine Payload Unit
  id_matches : machine.id = adv_id
  communication_set_is_singleton_backdoor_to_environment :
    ∃ p, machine.communication_set = {p} ∧
      p.dest = env_id ∧ p.label = .backdoor

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

/-- 环境调用 main machine 时是否提供了合法的 external identity。 -/
def environment_source_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (envelope : Envelope Payload) : Prop :=
  if _h_adv : envelope.port.dest = adv_id then
    True
  else
    ∃ ext_id,
      envelope.message.source = some ext_id ∧
        ext_id ∈ π.external_identities_of envelope.port.dest

/-- core 层检查腐化指令是否越过固定 static corruption set。 -/
def corruption_instruction_valid {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E) (envelope : Envelope Payload) : Prop :=
  match envelope.message.instruction with
  | .plain => True
  | .dummyCaller _ => True
  | .dummyDestination _ => True
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
      True)

/--
Controller 在投递前认证消息来源。

普通 P2P 消息的 `source` 总是覆盖为当前发送 machine 的 identity。唯一例外是
environment 调用 main machine：此时保留 environment 提供并已由
`environment_source_valid` 检查的 external identity。
-/
def authenticated_message {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E)
    (sender_id : MachineId) (envelope : Envelope Payload) : Message Payload :=
  if _h_env : sender_id = env_id then
    if _h_adv : envelope.port.dest = adv_id then
      { envelope.message with source := some env_id }
    else
      envelope.message
  else
    { envelope.message with source := some sender_id }

@[simp] theorem authenticated_message_of_sender_ne_environment
    {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (sender_id : MachineId)
    (envelope : Envelope Payload) (h_sender : sender_id ≠ env_id) :
    (setup.authenticated_message sender_id envelope).source = some sender_id := by
  have h_sender' : sender_id ≠ 0 := by simpa [env_id] using h_sender
  simp [authenticated_message, env_id, h_sender']

@[simp] theorem authenticated_message_environment_to_adversary
    {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (envelope : Envelope Payload)
    (h_dest : envelope.port.dest = adv_id) :
    (setup.authenticated_message env_id envelope).source = some env_id := by
  simp [authenticated_message, env_id, adv_id, h_dest]

theorem authenticated_message_environment_to_non_adversary
    {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (envelope : Envelope Payload)
    (h_dest : envelope.port.dest ≠ adv_id) :
    setup.authenticated_message env_id envelope = envelope.message := by
  have h_dest' : envelope.port.dest ≠ 1 := by simpa [adv_id] using h_dest
  simp [authenticated_message, env_id, adv_id, h_dest']

end ExecutionSetup

/-- 运行时的一个 protocol machine 局部状态。 -/
structure ProtocolMachineState (Payload : Type u) where
  Out : Type
  machine : Machine Payload Out
  state : machine.program.LocalState

namespace ProtocolMachineState

/-- 从 protocol 提供的异质 machine state 初始化运行时状态。 -/
def of_any_machine_state {Payload : Type u}
    (st : AnyMachineState Payload) : ProtocolMachineState Payload :=
  { Out := st.1.1
    machine := st.1.2
    state := st.2 }

/-- 运行时状态对应的 machine identity。 -/
def id {Payload : Type u} (st : ProtocolMachineState Payload) : MachineId :=
  st.machine.id

/-- 激活该 machine 一次。 -/
noncomputable def activate {Payload : Type u}
    (st : ProtocolMachineState Payload) :
    Option (Message Payload) →
    PMF (ProtocolMachineState Payload × Option (Envelope Payload)) :=
  fun incoming? =>
  (st.machine.program.activate st.state incoming?).bind fun result =>
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

/-- 激活环境一次。 -/
noncomputable def activate_environment {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E)
    (st : ControllerState _setup) (incoming? : Option (Message Payload)) :
    PMF (ControllerState _setup × Option (Envelope Payload)) :=
  (E.machine.program.activate st.env_state incoming?).bind fun result =>
    PMF.pure
      ({ st with env_state := result.state, active_id := env_id },
        result.outgoing?)

/-- 激活 adversary 一次。 -/
noncomputable def activate_adversary {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (_setup : ExecutionSetup π A E)
    (st : ControllerState _setup) (incoming? : Option (Message Payload)) :
    PMF (ControllerState _setup × Option (Envelope Payload)) :=
  (A.machine.program.activate st.adv_state incoming?).bind fun result =>
    PMF.pure
      ({ st with adv_state := result.state, active_id := adv_id },
        result.outgoing?)

/-- 激活某个 protocol machine 一次。 -/
noncomputable def activate_protocol_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    {setup : ExecutionSetup π A E}
    (st : ControllerState setup) (mid : MachineId)
    (incoming? : Option (Message Payload)) :
    PMF (ControllerState setup × Option (Envelope Payload)) :=
  match find_protocol_state? st mid with
  | none =>
      PMF.pure ({ st with active_id := env_id }, none)
  | some machine_state =>
      (ProtocolMachineState.activate machine_state incoming?).bind fun result =>
        PMF.pure ({ (replace_protocol_state st result.1) with active_id := mid }, result.2)

/-- 按 identity 激活一台运行时 machine。 -/
noncomputable def activate_machine {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E)
    (st : ControllerState setup) (mid : MachineId)
    (incoming? : Option (Message Payload)) :
    PMF (ControllerState setup × Option (Envelope Payload)) :=
  if _h_env : mid = env_id then
    activate_environment setup st incoming?
  else if _h_adv : mid = adv_id then
    activate_adversary setup st incoming?
  else
    activate_protocol_machine st mid incoming?

/--
在 activation 预算 `fuel` 内运行 controller。

每次调用某个 machine 的 `activate` 消耗一步预算。若当前 activation 产生合法
envelope，controller 立即把其中的 `Message` 投递给目标 machine 并递归激活
目标；若 machine 挂起、发出非法消息或路由失败，则控制回到环境。
-/
noncomputable def run_activation {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) :
    Nat → ControllerState setup → Option (Message Payload) →
      PMF (ControllerState setup)
  | 0, st, _ => PMF.pure st
  | fuel + 1, st, incoming? => by
      classical
      if environment_halted st then
        exact PMF.pure st
      else
        exact (activate_machine setup st st.active_id incoming?).bind fun result =>
          let st' := result.1
          match result.2 with
          | none =>
              run_activation setup fuel ({ st' with active_id := env_id }) none
          | some msg =>
              if h_valid : setup.outgoing_message_valid st.active_id msg then
                let incoming_message := setup.authenticated_message st.active_id msg
                if h_sys : setup.routes_to_system_machine msg.port.dest then
                  if _h_env : msg.port.dest = env_id then
                    run_activation setup fuel ({ st' with active_id := env_id })
                      (some incoming_message)
                  else if _h_adv : msg.port.dest = adv_id then
                    run_activation setup fuel ({ st' with active_id := adv_id })
                      (some incoming_message)
                  else
                    run_activation setup fuel ({ st' with active_id := msg.port.dest })
                      (some incoming_message)
                else if h_ext :
                    st.active_id ≠ env_id ∧
                    setup.routes_to_external_identity msg.port.dest ∧
                    msg.message.label = .subroutineOutput then
                  run_activation setup fuel ({ st' with active_id := env_id })
                    (some incoming_message)
                else
                  run_activation setup fuel ({ st' with active_id := env_id }) none
              else
                run_activation setup fuel ({ st' with active_id := env_id }) none

/--
在步数预算 `fuel` 内运行 controller。

这里的步数就是 machine activation 次数，而不是“环境轮次”。
-/
noncomputable def run_steps {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (fuel : Nat)
    (st : ControllerState setup) : PMF (ControllerState setup) :=
  run_activation setup fuel st none

/--
在步数预算内运行 controller，并记录是正常 halt 还是耗尽预算。

若初始状态或某次调度后环境 halt，返回 `.halted`；
若 fuel 用尽且环境仍未 halt，返回 `.budget_exceeded`。
-/
noncomputable def run_steps_with_status {Payload : Type u} {π : Protocol Payload}
    {A : Adversary Payload} {E : Environment Payload}
    (setup : ExecutionSetup π A E) (fuel : Nat)
    (st : ControllerState setup) : PMF (ControllerState setup × ExitStatus) :=
  (run_steps setup fuel st).bind fun st' =>
    PMF.pure
      (st', if environment_halted st' then ExitStatus.halted else ExitStatus.budget_exceeded)

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

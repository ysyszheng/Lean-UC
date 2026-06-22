import LeanCryptoProtocols.Assumptions.DDH
import LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE.Certificate.Certificate

/-!
# DHKE 子证明的 controller-level 模型

本文件只刻画 EasyUC SMC 证明中的 key exchange 子步骤。真实世界使用
两个 DH party 与两个 `Forw`；理想世界使用 `IdealKE` 和自动生成的 dummy
parties。
-/

set_option linter.flexible false
set_option linter.style.nativeDecide false

universe u

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

open LeanCryptoProtocols.Assumptions
open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality

/-! ## Simulator -/

/-- 封装 adversary 时，两个 one-shot `Forw.release` 依次对应 KE 的两次 release。 -/
inductive SimulatorStage where
  | waiting_init_release
  | waiting_confirm_release
  | done
  deriving Repr, DecidableEq

inductive PendingAdversaryInput where
  | first_observe
  | second_observe
  deriving Repr, DecidableEq

/-- simulator 给被封装 adversary 展示的两条 `Forw.observe` 视图。 -/
structure SimulatorView where
  first_share : GroupElement
  second_share : GroupElement
  deriving Repr, DecidableEq

/-- `dhke_simulator A` 的局部状态：保留被封装 adversary 的局部状态与 release 阶段。 -/
structure SimulatorState (A : Adversary SMCEasyUCPayload) where
  sec_param : ℕ
  wrapped_state : A.machine.program.LocalState
  stage : SimulatorStage
  sampled_view? : Option SimulatorView
  pending_input : Option PendingAdversaryInput

/-- simulator 到环境的唯一静态 backdoor 端口。 -/
def simulator_to_environment_port : CommPort :=
  mk_backdoor_port adv_id env_id (by decide) (Or.inl rfl)

/-- simulator 运行时通过 overlay 发给 `IdealKE` 的 backdoor 端口。 -/
def simulator_to_ideal_ke_port : CommPort :=
  mk_backdoor_port adv_id ideal_ke_id (by decide) (Or.inl rfl)

private def release_init_envelope : Envelope SMCEasyUCPayload :=
  { port := simulator_to_ideal_ke_port
    message := {
      source := some adv_id
      label := .backdoor
      payload := .ke_plain .release_init
    }
    label_matches := rfl
  }

private def release_confirm_envelope : Envelope SMCEasyUCPayload :=
  { port := simulator_to_ideal_ke_port
    message := {
      source := some adv_id
      label := .backdoor
      payload := .ke_plain .release_confirm
    }
    label_matches := rfl
  }

private def adversary_requested_release (payload : SMCEasyUCPayload) : Bool :=
  match payload with
  | .forw_plain .release => true
  | .forw_to_functionality _ .release => true
  | _ => false

private def first_observe_message
    (share : GroupElement) : Message SMCEasyUCPayload := {
  source := some forw_ke_forward_id
  label := .backdoor
  payload := .forw_plain
    (.observe ke_sender_id ke_receiver_id (.ke_first share))
}

private def second_observe_message
    (share : GroupElement) : Message SMCEasyUCPayload := {
  source := some forw_ke_return_id
  label := .backdoor
  payload := .forw_plain
    (.observe ke_receiver_id ke_sender_id (.ke_second share))
}

private def translate_release
    (stage : SimulatorStage) (payload : SMCEasyUCPayload) :
    SimulatorStage × Option (Envelope SMCEasyUCPayload) :=
  if adversary_requested_release payload then
    match stage with
    | .waiting_init_release => (.waiting_confirm_release, some release_init_envelope)
    | .waiting_confirm_release => (.done, some release_confirm_envelope)
    | .done => (.done, none)
  else
    (stage, none)

private def translate_adversary_outgoing
    (stage : SimulatorStage) (env : Envelope SMCEasyUCPayload) :
    SimulatorStage × Option (Envelope SMCEasyUCPayload) :=
  if adversary_requested_release env.message.payload then
    translate_release stage env.message.payload
  else if env.port.dest = env_id ∧ env.message.label = .backdoor then
    (stage, some {
      port := simulator_to_environment_port
      message := {
        source := some adv_id
        label := .backdoor
        payload := env.message.payload
      }
      label_matches := rfl
    })
  else
    (stage, none)

private noncomputable def sample_simulator_view
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF SimulatorView :=
  (ddh_random gen n).bind fun sample =>
    PMF.pure {
      first_share := ⟨sample.1.encode sample.2.gx⟩
      second_share := ⟨sample.1.encode sample.2.gy⟩
    }

private noncomputable def ensure_simulator_view
    (gen : GroupGenerator.{0}) (fixed_view? : Option SimulatorView)
    {A : Adversary SMCEasyUCPayload}
    (st : SimulatorState A) : PMF (SimulatorView × SimulatorState A) :=
  match fixed_view? with
  | some view => PMF.pure (view, st)
  | none =>
      match st.sampled_view? with
      | some view => PMF.pure (view, st)
      | none =>
          (sample_simulator_view gen st.sec_param).bind fun view =>
            PMF.pure (view, { st with sampled_view? := some view })

private noncomputable def deliver_pending_to_adversary
    (gen : GroupGenerator.{0}) (fixed_view? : Option SimulatorView)
    (A : Adversary SMCEasyUCPayload)
    (st : SimulatorState A) :
    PMF (SimulatorState A) :=
  match st.pending_input with
  | none =>
      PMF.pure st
  | some .first_observe =>
      (ensure_simulator_view gen fixed_view? st).bind fun view_and_state =>
        let view := view_and_state.1
        let st_view := view_and_state.2
        let wrapped_state :=
          A.machine.program.receive st_view.wrapped_state
            (first_observe_message view.first_share)
        PMF.pure {
          st_view with
            wrapped_state := wrapped_state
            pending_input := none
        }
  | some .second_observe =>
      (ensure_simulator_view gen fixed_view? st).bind fun view_and_state =>
        let view := view_and_state.1
        let st_view := view_and_state.2
        let wrapped_state :=
          A.machine.program.receive st_view.wrapped_state
            (second_observe_message view.second_share)
        PMF.pure {
          st_view with
            wrapped_state := wrapped_state
            pending_input := none
        }

noncomputable def simulator_program
    (gen : GroupGenerator.{0}) (fixed_view? : Option SimulatorView)
    (A : Adversary SMCEasyUCPayload) :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := SimulatorState A
  init := fun n => {
    sec_param := n
    wrapped_state := A.machine.program.init n
    stage := .waiting_init_release
    sampled_view? := fixed_view?
    pending_input := none
  }
  receive := fun st msg =>
    match msg.payload with
    | .ke_plain (.observe_init _ _) =>
        { st with pending_input := some .first_observe }
    | .ke_plain .observe_confirm =>
        { st with pending_input := some .second_observe }
    | _ =>
        let wrapped_state := A.machine.program.receive st.wrapped_state msg
        { st with wrapped_state := wrapped_state }
  resume := fun st =>
    (deliver_pending_to_adversary gen fixed_view? A st).bind fun st_delivered =>
      (A.machine.program.resume st_delivered.wrapped_state).bind fun wrapped_result =>
        let st' : SimulatorState A := {
          st_delivered with
          wrapped_state := wrapped_result.state
        }
        match wrapped_result.outgoing? with
        | none =>
            PMF.pure {
              state := st'
              outgoing? := none
            }
        | some env =>
            let translated := translate_adversary_outgoing st'.stage env
            PMF.pure {
              state := { st' with stage := translated.1 }
              outgoing? := translated.2
            }
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def simulator_machine
    (gen : GroupGenerator.{0}) (fixed_view? : Option SimulatorView)
    (A : Adversary SMCEasyUCPayload) : Machine SMCEasyUCPayload Unit where
  id := adv_id
  communication_set := {simulator_to_environment_port}
  program := simulator_program gen fixed_view? A
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [simulator_to_environment_port] at hp
      rcases hp with rfl
      rfl
    · intro p₁ hp₁ p₂ hp₂ _h_dest
      simp [simulator_to_environment_port] at hp₁ hp₂
      rcases hp₁ with rfl
      rcases hp₂ with rfl
      rfl

/--
固定的 DHKE simulator 构造。

它不是直接复用 adversary：新的 machine 只有 simulator 的通信接口；
程序内部黑盒调用 `A.machine.program.receive/resume`，并把两条 `Forw.release`
按阶段翻译为 `IdealKE.release_init` 与 `IdealKE.release_confirm`。
-/
noncomputable def simulator
    (gen : GroupGenerator)
    (A : Adversary SMCEasyUCPayload) : Simulator SMCEasyUCPayload where
  machine := simulator_machine gen none A
  id_matches := rfl
  unique_backdoor_port_to_environment := by
    refine ⟨simulator_to_environment_port, ?_, ?_⟩
    · refine ⟨?_, rfl, rfl⟩
      simp [simulator_machine, simulator_to_environment_port]
    · intro y hy
      rcases hy with ⟨hy_mem, _hy_dest, _hy_label⟩
      simp [simulator_machine, simulator_to_environment_port] at hy_mem
      rcases hy_mem with rfl
      rfl

/-! ## DDH challenge-programmed executions -/

/-- DDH challenge 中的第一条 DH share `X`。 -/
def challenge_first_share (sample : DDHSample.{0}) : GroupElement :=
  ⟨sample.1.encode sample.2.gx⟩

/-- DDH challenge 中的第二条 DH share `Y`。 -/
def challenge_second_share (sample : DDHSample.{0}) : GroupElement :=
  ⟨sample.1.encode sample.2.gy⟩

/-- DDH challenge 中用于替换 session key 的元素 `Z`。 -/
def challenge_shared_key (sample : DDHSample.{0}) : SharedKey :=
  ⟨sample.1.encode sample.2.gz⟩

/-- DDH-real witness 的第一条公开 share 与 challenge 的第一条 share 相同。 -/
theorem challenge_first_share_of_witness
    (witness : DDHRealWitness) :
    challenge_first_share witness.to_sample =
      witness.initiator_secret.public_share := by
  simp [challenge_first_share, DDHRealWitness.to_sample,
    DDHRealWitness.initiator_secret]

/-- DDH-real witness 的第二条公开 share 与 challenge 的第二条 share 相同。 -/
theorem challenge_second_share_of_witness
    (witness : DDHRealWitness) :
    challenge_second_share witness.to_sample =
      witness.responder_secret.public_share := by
  simp [challenge_second_share, DDHRealWitness.to_sample,
    DDHRealWitness.responder_secret]

/-- DDH-real witness 的 challenge key 是 `g^(ab)` 的编码。 -/
theorem challenge_shared_key_of_witness
    (witness : DDHRealWitness) :
    challenge_shared_key witness.to_sample =
      ⟨witness.G.encode
        (witness.G.pow witness.G.generator
          (witness.G.mul_exp witness.initiator_exponent
            witness.responder_exponent))⟩ := by
  simp [challenge_shared_key, DDHRealWitness.to_sample]

/-- initiator 用 witness secret 和 responder share 派生的 key 等于 challenge key。 -/
theorem initiator_derive_key_eq_challenge_shared_key
    (witness : DDHRealWitness) :
    derive_key_from_secret witness.initiator_secret
        witness.responder_secret.public_share =
      challenge_shared_key witness.to_sample := by
  rw [challenge_shared_key_of_witness]
  exact derive_key_from_secret_generator witness.G
    witness.initiator_exponent witness.responder_exponent

/-- responder 用 witness secret 和 initiator share 派生的 key 等于 challenge key。 -/
theorem responder_derive_key_eq_challenge_shared_key
    (witness : DDHRealWitness) :
    derive_key_from_secret witness.responder_secret
        witness.initiator_secret.public_share =
      challenge_shared_key witness.to_sample := by
  rw [challenge_shared_key_of_witness]
  calc
    derive_key_from_secret witness.responder_secret
        witness.initiator_secret.public_share
        = derive_key_from_secret witness.initiator_secret
            witness.responder_secret.public_share := by
          exact (derive_key_from_secret_comm witness.G
            witness.initiator_exponent witness.responder_exponent).symm
    _ = ⟨witness.G.encode
          (witness.G.pow witness.G.generator
            (witness.G.mul_exp witness.initiator_exponent
              witness.responder_exponent))⟩ := by
          exact derive_key_from_secret_generator witness.G
            witness.initiator_exponent witness.responder_exponent

/-- DDH challenge 对应的理想 KE key material。 -/
def challenge_ideal_key_material (sample : DDHSample.{0}) : KEIdealKeyMaterial := {
  shared_key := challenge_shared_key sample
}

/-- DDH challenge 编程时 simulator 展示给 adversary 的两条网络观察。 -/
def challenge_simulator_view (sample : DDHSample.{0}) : SimulatorView := {
  first_share := challenge_first_share sample
  second_share := challenge_second_share sample
}

/--
DDH-random challenge-ideal 中共享同一个 sample 的两个分离组件。

`simulator_view` 只供 challenge-programmed simulator 伪造 `Forw.observe`
中的两条 DH public share；`key_material` 只供 `IdealKE` 输出 session key。
这避免把真实 DH transcript 放入 ideal functionality 的语义。
-/
structure IdealChallengeComponents where
  simulator_view : SimulatorView
  key_material : KEIdealKeyMaterial
  deriving Repr, DecidableEq

/-- 从一个 DDH sample 投影出 challenge-ideal 的分离组件。 -/
def ideal_challenge_components_of_sample
    (sample : DDHSample.{0}) : IdealChallengeComponents := {
  simulator_view := challenge_simulator_view sample
  key_material := challenge_ideal_key_material sample
}

/--
DDH-random challenge-ideal 的联合采样器。

后续 `H4 = H5` 的 sampler lifting 应把标准 ideal execution 中
“simulator 采样 fake shares” 与 “IdealKE 采样 key” 的联合分布提升到这个
DDH-random 投影。
-/
noncomputable def sample_ideal_challenge_components
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF IdealChallengeComponents :=
  (ddh_random gen n).bind fun sample =>
    PMF.pure (ideal_challenge_components_of_sample sample)

/-- 上面的联合采样器按定义就是 DDH-random sample 的 share/key 分离投影。 -/
theorem sample_ideal_challenge_components_eq_ddh_random
    (gen : GroupGenerator.{0}) (n : ℕ) :
    sample_ideal_challenge_components gen n =
      (ddh_random gen n).bind fun sample =>
        PMF.pure (ideal_challenge_components_of_sample sample) := by
  rfl

/--
DDH challenge 编程的 simulator。

它与标准 `simulator gen A` 使用相同的通信接口和 release 翻译逻辑，只是把
发送给被封装 adversary 的两条 `Forw.observe` 视图固定为 challenge 中的
`X = g^a` 与 `Y = g^b`。
-/
noncomputable def challenge_simulator
    (gen : GroupGenerator)
    (sample : DDHSample.{0})
    (A : Adversary SMCEasyUCPayload) : Simulator SMCEasyUCPayload where
  machine := simulator_machine gen (some (challenge_simulator_view sample)) A
  id_matches := rfl
  unique_backdoor_port_to_environment := by
    refine ⟨simulator_to_environment_port, ?_, ?_⟩
    · refine ⟨?_, rfl, rfl⟩
      simp [simulator_machine, simulator_to_environment_port]
    · intro y hy
      rcases hy with ⟨hy_mem, _hy_dest, _hy_label⟩
      simp [simulator_machine, simulator_to_environment_port] at hy_mem
      rcases hy_mem with rfl
      rfl

/-- 用 DDH challenge 的 key component 固定理想 KE 功能机的 key sampler。 -/
noncomputable def challenge_ideal_ke_ids
    (gen : GroupGenerator) (sample : DDHSample.{0}) : KEIds :=
  { ideal_ke_ids gen with
    sample_key_material := fun _ => PMF.pure (challenge_ideal_key_material sample) }

/-- DDH challenge 编程的理想 KE 功能。 -/
noncomputable def challenge_ideal_ke_functionality
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    IdealFunctionality SMCEasyUCPayload :=
  IdealKE (challenge_ideal_ke_ids gen sample)

/-- DDH challenge 编程的理想 KE protocol。 -/
noncomputable def challenge_ideal_protocol
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    Protocol SMCEasyUCPayload :=
  (mk_ideal_protocol (challenge_ideal_ke_functionality gen sample)).protocol

/-- challenge ideal protocol 与标准 ideal KE protocol 有相同的 machine identity。 -/
theorem challenge_ideal_machine_ids_eq_ideal
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    machine_ids (challenge_ideal_protocol gen sample).machines =
      machine_ids ((mk_ideal_protocol (ideal_ke_functionality gen)).protocol.machines) := by
  unfold challenge_ideal_protocol
  rw [mk_ideal_protocol_machine_ids]
  rw [mk_ideal_protocol_machine_ids]
  simp [challenge_ideal_ke_functionality,
    ideal_ke_functionality, challenge_ideal_ke_ids, ideal_ke_ids, IdealKE]

/-- challenge ideal protocol 与标准 ideal KE protocol 有相同的 main-machine 判断。 -/
theorem challenge_ideal_is_main_machine_iff
    (gen : GroupGenerator) (sample : DDHSample.{0}) (mid : MachineId) :
    (challenge_ideal_protocol gen sample).is_main_machine mid ↔
      ((mk_ideal_protocol (ideal_ke_functionality gen)).protocol).is_main_machine mid := by
  unfold challenge_ideal_protocol
  rw [mk_ideal_protocol_is_main_machine_iff]
  rw [mk_ideal_protocol_is_main_machine_iff]
  simp [challenge_ideal_ke_functionality, challenge_ideal_ke_ids,
    ideal_ke_functionality, ideal_ke_ids, IdealKE]

/-- challenge ideal protocol 与标准 ideal KE protocol 有相同的 internal-machine 判断。 -/
theorem challenge_ideal_is_internal_machine_iff
    (gen : GroupGenerator) (sample : DDHSample.{0}) (mid : MachineId) :
    (challenge_ideal_protocol gen sample).is_internal_machine mid ↔
      ((mk_ideal_protocol (ideal_ke_functionality gen)).protocol).is_internal_machine mid := by
  unfold challenge_ideal_protocol
  rw [mk_ideal_protocol_is_internal_machine_iff]
  rw [mk_ideal_protocol_is_internal_machine_iff]
  simp [challenge_ideal_ke_functionality, challenge_ideal_ke_ids,
    ideal_ke_functionality, ideal_ke_ids, IdealKE]

inductive ChallengeInitiatorAction where
  | send_first
  | output_key
  deriving Repr, DecidableEq

inductive ChallengeInitiatorPhase where
  | waiting_init
  | waiting_second
  | done
  deriving Repr, DecidableEq

inductive ChallengeResponderPhase where
  | waiting_first
  | sent_second
  | done
  deriving Repr, DecidableEq

structure ChallengeInitiatorState where
  phase : ChallengeInitiatorPhase
  pending_action : Option ChallengeInitiatorAction
  deriving Repr, DecidableEq

structure ChallengeResponderState where
  phase : ChallengeResponderPhase
  pending_first_share : Option GroupElement
  pending_outgoing : Option (Envelope SMCEasyUCPayload)
  deriving Repr, DecidableEq

def challenge_initiator_init (_n : ℕ) : ChallengeInitiatorState := {
  phase := .waiting_init
  pending_action := none
}

def challenge_responder_init (_n : ℕ) : ChallengeResponderState := {
  phase := .waiting_first
  pending_first_share := none
  pending_outgoing := none
}

def challenge_initiator_receive
    (st : ChallengeInitiatorState)
    (msg : Message SMCEasyUCPayload) :
    ChallengeInitiatorState :=
  match st.phase, msg.label, msg.payload with
  | .waiting_init, .input, .ke_plain .init =>
      { st with
        phase := .waiting_second
        pending_action := some .send_first }
  | .waiting_second, .subroutineOutput,
      .forw_from_functionality _ (.delivered _ _ (.ke_second _share)) =>
      { st with pending_action := some .output_key }
  | _, _, _ =>
      st

def challenge_responder_receive
    (st : ChallengeResponderState)
    (msg : Message SMCEasyUCPayload) :
    ChallengeResponderState :=
  match st.phase, msg.label, msg.payload with
  | .waiting_first, .subroutineOutput,
      .forw_from_functionality _ (.delivered _ _ (.ke_first share)) =>
      { st with pending_first_share := some share }
  | _, _, _ =>
      st

def challenge_initiator_first_envelope
    (sample : DDHSample.{0}) : Envelope SMCEasyUCPayload :=
  { port := ke_sender_to_forw_ke_forward_port
    message := {
      source := some ke_sender_id
      label := .input
      payload := .forw_plain
        (.submit ke_sender_id ke_receiver_id
          (.ke_first (challenge_first_share sample)))
    }
    label_matches := rfl
  }

def challenge_responder_second_envelope
    (sample : DDHSample.{0}) : Envelope SMCEasyUCPayload :=
  { port := ke_receiver_to_forw_ke_return_port
    message := {
      source := some ke_receiver_id
      label := .input
      payload := .forw_plain
        (.submit ke_receiver_id ke_sender_id
          (.ke_second (challenge_second_share sample)))
    }
    label_matches := rfl
  }

def challenge_initiator_key_envelope
    (sample : DDHSample.{0}) : Envelope SMCEasyUCPayload :=
  initiator_key_envelope (challenge_shared_key sample)

def challenge_responder_key_envelope
    (sample : DDHSample.{0}) : Envelope SMCEasyUCPayload :=
  responder_key_envelope (challenge_shared_key sample)

/-! ## Real-to-challenge local-state projections -/

/--
把真实 initiator 的 phase 投影到 DDH challenge-programmed initiator 的 phase。

该投影丢弃 secret exponent，只保留 controller trace 中可观察的控制状态。
-/
def project_initiator_phase : InitiatorPhase → ChallengeInitiatorPhase
  | .waiting_init => .waiting_init
  | .waiting_second => .waiting_second
  | .done => .done

/-- 把真实 initiator 的 pending action 投影到 challenge action。 -/
def project_initiator_action : InitiatorAction → ChallengeInitiatorAction
  | .send_first => .send_first
  | .output_key _ => .output_key

/-- 真实 initiator 局部状态到 challenge initiator 局部状态的投影。 -/
def project_initiator_state (st : InitiatorState) : ChallengeInitiatorState := {
  phase := project_initiator_phase st.phase
  pending_action := st.pending_action.map project_initiator_action
}

/-- 把真实 responder 的 phase 投影到 DDH challenge-programmed responder 的 phase。 -/
def project_responder_phase : ResponderPhase → ChallengeResponderPhase
  | .waiting_first => .waiting_first
  | .sent_second => .sent_second
  | .done => .done

/--
真实 responder 的 pending peer share 投影。

在 witness-coupled trace 中，任何 reachable 的 pending peer share 都应等于
`sample` 的第一条 DDH share；投影函数只保留“已经收到第一条 share”这一控制事实。
-/
def project_responder_pending_first
    (sample : DDHSample.{0}) : Option GroupElement → Option GroupElement
  | none => none
  | some _ => some (challenge_first_share sample)

/--
真实 responder 暂存的输出 envelope 投影。

在 witness-coupled trace 中，reachable 的 pending output 是 witness 对应 key；
challenge 侧只需要保留“下一步会输出 challenge key”这一控制事实。
-/
def project_responder_pending_outgoing
    (sample : DDHSample.{0}) :
    Option (Envelope SMCEasyUCPayload) → Option (Envelope SMCEasyUCPayload)
  | none => none
  | some _ => some (challenge_responder_key_envelope sample)

/-- 真实 responder 局部状态到 challenge responder 局部状态的投影。 -/
def project_responder_state
    (sample : DDHSample.{0}) (st : ResponderState) : ChallengeResponderState := {
  phase := project_responder_phase st.phase
  pending_first_share := project_responder_pending_first sample st.pending_peer_share
  pending_outgoing := project_responder_pending_outgoing sample st.pending_outgoing
}

/-- initiator 的一次 activation result 投影。 -/
def project_initiator_activation_result
    (result : ActivationResult SMCEasyUCPayload InitiatorState) :
    ActivationResult SMCEasyUCPayload ChallengeInitiatorState := {
  state := project_initiator_state result.state
  outgoing? := result.outgoing?
}

/-- responder 的一次 activation result 投影。 -/
def project_responder_activation_result
    (sample : DDHSample.{0})
    (result : ActivationResult SMCEasyUCPayload ResponderState) :
    ActivationResult SMCEasyUCPayload ChallengeResponderState := {
  state := project_responder_state sample result.state
  outgoing? := result.outgoing?
}

/-- witness 初始化的真实 initiator 状态投影后是 challenge initiator 初始状态。 -/
theorem project_initiator_state_of_witness_initial
    (n : ℕ) (witness : DDHRealWitness) :
    project_initiator_state
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_init
        pending_action := none } =
      challenge_initiator_init n := by
  rfl

/-- witness 初始化的真实 responder 状态投影后是 challenge responder 初始状态。 -/
theorem project_responder_state_of_witness_initial
    (n : ℕ) (witness : DDHRealWitness) :
    project_responder_state witness.to_sample
      { sec_param := n
        group? := some witness.G
        secret? := some witness.responder_secret
        phase := .waiting_first
        pending_peer_share := none
        pending_outgoing := none } =
      challenge_responder_init n := by
  rfl

/-- 外层 caller 发给 DHKE initiator 的合法初始化消息。 -/
def initiator_init_message : Message SMCEasyUCPayload := {
  source := some smc_sender_id
  label := .input
  payload := .ke_plain .init
}

/-- 第一条 `Forw` 交付给 responder 的合法消息。 -/
def first_share_delivered_message
    (sample : DDHSample.{0}) : Message SMCEasyUCPayload := {
  source := some forw_ke_forward_id
  label := .subroutineOutput
  payload := .forw_from_functionality smc_receiver_id
    (.delivered ke_sender_id ke_receiver_id
      (.ke_first (challenge_first_share sample)))
}

/-- 第二条 `Forw` 交付给 initiator 的合法消息。 -/
def second_share_delivered_message
    (sample : DDHSample.{0}) : Message SMCEasyUCPayload := {
  source := some forw_ke_return_id
  label := .subroutineOutput
  payload := .forw_from_functionality smc_sender_id
    (.delivered ke_receiver_id ke_sender_id
      (.ke_second (challenge_second_share sample)))
}

/-- 真实 initiator 收到合法初始化消息后进入等待发送第一条 share 的状态。 -/
theorem initiator_receive_init_of_witness
    (n : ℕ) (witness : DDHRealWitness) :
    initiator_receive
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_init
        pending_action := none }
      initiator_init_message =
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action := some .send_first } := by
  simp [initiator_receive, initiator_init_message]

/-- challenge initiator 收到合法初始化消息后进入同构的 pending 状态。 -/
theorem challenge_initiator_receive_init
    (st : ChallengeInitiatorState)
    (h_phase : st.phase = .waiting_init) :
    challenge_initiator_receive st initiator_init_message =
      { st with
        phase := .waiting_second
        pending_action := some .send_first } := by
  rcases st with ⟨phase, pending_action⟩
  simp at h_phase
  subst phase
  simp [challenge_initiator_receive, initiator_init_message]

/-- witness 初始 initiator 收到 init 时，真实 receive 与 challenge receive 在投影下交换。 -/
theorem project_initiator_receive_init_of_witness
    (n : ℕ) (witness : DDHRealWitness) :
    project_initiator_state
      (initiator_receive
        { sec_param := n
          group? := some witness.G
          secret? := some witness.initiator_secret
          phase := .waiting_init
          pending_action := none }
        initiator_init_message) =
      challenge_initiator_receive
        (project_initiator_state
          { sec_param := n
            group? := some witness.G
            secret? := some witness.initiator_secret
            phase := .waiting_init
            pending_action := none })
        initiator_init_message := by
  simp [initiator_receive, challenge_initiator_receive, initiator_init_message,
    project_initiator_state, project_initiator_phase, project_initiator_action]

/-- 真实 responder 收到第一条合法 share 后暂存该 share。 -/
theorem responder_receive_first_share_of_witness
    (n : ℕ) (witness : DDHRealWitness) :
    responder_receive
      { sec_param := n
        group? := some witness.G
        secret? := some witness.responder_secret
        phase := .waiting_first
        pending_peer_share := none
        pending_outgoing := none }
      (first_share_delivered_message witness.to_sample) =
      { sec_param := n
        group? := some witness.G
        secret? := some witness.responder_secret
        phase := .waiting_first
        pending_peer_share := some witness.initiator_secret.public_share
        pending_outgoing := none } := by
  simp [responder_receive, first_share_delivered_message,
    challenge_first_share_of_witness]

/-- challenge responder 收到第一条合法 share 后进入同构 pending 状态。 -/
theorem challenge_responder_receive_first_share
    (sample : DDHSample.{0}) (st : ChallengeResponderState)
    (h_phase : st.phase = .waiting_first) :
    challenge_responder_receive st (first_share_delivered_message sample) =
      { st with
        pending_first_share := some (challenge_first_share sample) } := by
  rcases st with ⟨phase, pending_first_share, pending_outgoing⟩
  simp at h_phase
  subst phase
  simp [challenge_responder_receive, first_share_delivered_message]

/-- witness responder 收到第一条 share 时，真实 receive 与 challenge receive 在投影下交换。 -/
theorem project_responder_receive_first_share_of_witness
    (n : ℕ) (witness : DDHRealWitness) :
    project_responder_state witness.to_sample
      (responder_receive
        { sec_param := n
          group? := some witness.G
          secret? := some witness.responder_secret
          phase := .waiting_first
          pending_peer_share := none
          pending_outgoing := none }
        (first_share_delivered_message witness.to_sample)) =
      challenge_responder_receive
        (project_responder_state witness.to_sample
          { sec_param := n
            group? := some witness.G
            secret? := some witness.responder_secret
            phase := .waiting_first
            pending_peer_share := none
            pending_outgoing := none })
        (first_share_delivered_message witness.to_sample) := by
  simp [responder_receive, challenge_responder_receive, first_share_delivered_message,
    project_responder_state, project_responder_phase, project_responder_pending_first,
    project_responder_pending_outgoing, challenge_first_share_of_witness]

/-- 真实 initiator 收到第二条合法 share 后准备输出 witness 对应的共享 key。 -/
theorem initiator_receive_second_share_of_witness
    (n : ℕ) (witness : DDHRealWitness) :
    initiator_receive
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action := none }
      (second_share_delivered_message witness.to_sample) =
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action :=
          some (.output_key witness.responder_secret.public_share) } := by
  simp [initiator_receive, second_share_delivered_message,
    challenge_second_share_of_witness]

/-- challenge initiator 收到第二条合法 share 后准备输出 challenge key。 -/
theorem challenge_initiator_receive_second_share
    (sample : DDHSample.{0}) (st : ChallengeInitiatorState)
    (h_phase : st.phase = .waiting_second) :
    challenge_initiator_receive st (second_share_delivered_message sample) =
      { st with
        pending_action := some .output_key } := by
  rcases st with ⟨phase, pending_action⟩
  simp at h_phase
  subst phase
  simp [challenge_initiator_receive, second_share_delivered_message]

/-- witness initiator 收到第二条 share 时，真实 receive 与 challenge receive 在投影下交换。 -/
theorem project_initiator_receive_second_share_of_witness
    (n : ℕ) (witness : DDHRealWitness) :
    project_initiator_state
      (initiator_receive
        { sec_param := n
          group? := some witness.G
          secret? := some witness.initiator_secret
          phase := .waiting_second
          pending_action := none }
        (second_share_delivered_message witness.to_sample)) =
      challenge_initiator_receive
        (project_initiator_state
          { sec_param := n
            group? := some witness.G
            secret? := some witness.initiator_secret
            phase := .waiting_second
            pending_action := none })
        (second_share_delivered_message witness.to_sample) := by
  simp [initiator_receive, challenge_initiator_receive, second_share_delivered_message,
    project_initiator_state, project_initiator_phase, project_initiator_action,
    challenge_second_share_of_witness]

/--
真实 initiator 在 witness secret 下处理 `.send_first` 时，发送的第一条网络消息
与 challenge-programmed initiator 相同。
-/
theorem initiator_resume_send_first_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    initiator_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action := some .send_first } =
      PMF.pure {
        state := {
          sec_param := n
          group? := some witness.G
          secret? := some witness.initiator_secret
          phase := .waiting_second
          pending_action := none
        }
        outgoing? := some (challenge_initiator_first_envelope witness.to_sample)
      } := by
  simp [initiator_resume, challenge_initiator_first_envelope,
    challenge_first_share, DDHRealWitness.to_sample,
    DDHRealWitness.initiator_secret]

/--
真实 initiator 在收到 responder share 后输出的 key，与 challenge-programmed
initiator 输出的 key 相同。
-/
theorem initiator_resume_output_key_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    initiator_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action :=
          some (.output_key witness.responder_secret.public_share) } =
      PMF.pure {
        state := {
          sec_param := n
          group? := some witness.G
          secret? := none
          phase := .done
          pending_action := none
        }
        outgoing? := some (challenge_initiator_key_envelope witness.to_sample)
      } := by
  simp [initiator_resume, challenge_initiator_key_envelope,
    initiator_derive_key_eq_challenge_shared_key]

/--
真实 responder 在 witness secret 下收到 initiator share 后，发送的第二条网络消息
和暂存的本地 key 输出都与 challenge-programmed responder 相同。
-/
theorem responder_resume_send_second_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    responder_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.responder_secret
        phase := .waiting_first
        pending_peer_share := some witness.initiator_secret.public_share
        pending_outgoing := none } =
      PMF.pure {
        state := {
          sec_param := n
          group? := some witness.G
          secret? := some witness.responder_secret
          phase := .sent_second
          pending_peer_share := none
          pending_outgoing :=
            some (challenge_responder_key_envelope witness.to_sample)
        }
        outgoing? := some (challenge_responder_second_envelope witness.to_sample)
      } := by
  have hkey_expanded :
      derive_key_from_secret
          { G := witness.G
            exponent := witness.responder_exponent
            public_share :=
              ⟨witness.G.encode
                (witness.G.pow witness.G.generator witness.responder_exponent)⟩ }
          witness.initiator_secret.public_share =
        challenge_shared_key witness.to_sample := by
    simpa [DDHRealWitness.responder_secret] using
      responder_derive_key_eq_challenge_shared_key witness
  simp [responder_resume, challenge_responder_second_envelope,
    challenge_responder_key_envelope, challenge_second_share,
    DDHRealWitness.to_sample, hkey_expanded, DDHRealWitness.responder_secret]

/-- responder 暂存 key 输出时，下一步会直接输出该 key。 -/
theorem responder_resume_pending_key
    (gen : GroupGenerator.{0}) (st : ResponderState)
    (env : Envelope SMCEasyUCPayload) :
    responder_resume gen { st with pending_outgoing := some env } =
      PMF.pure {
        state := { st with pending_outgoing := none, phase := .done }
        outgoing? := some env
      } := by
  simp [responder_resume]

noncomputable def challenge_initiator_resume
    (sample : DDHSample.{0})
    (st : ChallengeInitiatorState) :
    PMF (ActivationResult SMCEasyUCPayload ChallengeInitiatorState) :=
  match st.pending_action with
  | none =>
      PMF.pure {
        state := st
        outgoing? := none
      }
  | some .send_first =>
      PMF.pure {
        state := {
          st with
            phase := .waiting_second
            pending_action := none
        }
        outgoing? := some (challenge_initiator_first_envelope sample)
      }
  | some .output_key =>
      PMF.pure {
        state := {
          st with
            phase := .done
            pending_action := none
        }
        outgoing? := some (challenge_initiator_key_envelope sample)
      }

noncomputable def challenge_responder_resume
    (sample : DDHSample.{0})
    (st : ChallengeResponderState) :
    PMF (ActivationResult SMCEasyUCPayload ChallengeResponderState) :=
  match st.pending_outgoing with
  | some env =>
      PMF.pure {
        state := {
          st with
            phase := .done
            pending_outgoing := none
        }
        outgoing? := some env
      }
  | none =>
      match st.pending_first_share with
      | none =>
          PMF.pure {
            state := st
            outgoing? := none
          }
      | some _share =>
          PMF.pure {
            state := {
              st with
                phase := .sent_second
                pending_first_share := none
                pending_outgoing :=
                  some (challenge_responder_key_envelope sample)
            }
            outgoing? := some (challenge_responder_second_envelope sample)
          }

/-- initiator 发送第一条 share 的 resume 在 witness 投影下与 challenge resume 交换。 -/
theorem project_initiator_resume_send_first_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    (initiator_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action := some .send_first }).bind
        (fun result => PMF.pure (project_initiator_activation_result result)) =
      challenge_initiator_resume witness.to_sample
        (project_initiator_state
          { sec_param := n
            group? := some witness.G
            secret? := some witness.initiator_secret
            phase := .waiting_second
            pending_action := some .send_first }) := by
  rw [initiator_resume_send_first_of_witness]
  simp [challenge_initiator_resume, project_initiator_activation_result,
    project_initiator_state, project_initiator_phase, project_initiator_action]

/-- initiator 输出 key 的 resume 在 witness 投影下与 challenge resume 交换。 -/
theorem project_initiator_resume_output_key_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    (initiator_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.initiator_secret
        phase := .waiting_second
        pending_action :=
          some (.output_key witness.responder_secret.public_share) }).bind
        (fun result => PMF.pure (project_initiator_activation_result result)) =
      challenge_initiator_resume witness.to_sample
        (project_initiator_state
          { sec_param := n
            group? := some witness.G
            secret? := some witness.initiator_secret
            phase := .waiting_second
            pending_action :=
              some (.output_key witness.responder_secret.public_share) }) := by
  rw [initiator_resume_output_key_of_witness]
  simp [challenge_initiator_resume, project_initiator_activation_result,
    project_initiator_state, project_initiator_phase, project_initiator_action]

/-- responder 发送第二条 share 的 resume 在 witness 投影下与 challenge resume 交换。 -/
theorem project_responder_resume_send_second_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    (responder_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.responder_secret
        phase := .waiting_first
        pending_peer_share := some witness.initiator_secret.public_share
        pending_outgoing := none }).bind
        (fun result => PMF.pure
          (project_responder_activation_result witness.to_sample result)) =
      challenge_responder_resume witness.to_sample
        (project_responder_state witness.to_sample
          { sec_param := n
            group? := some witness.G
            secret? := some witness.responder_secret
            phase := .waiting_first
            pending_peer_share := some witness.initiator_secret.public_share
            pending_outgoing := none }) := by
  rw [responder_resume_send_second_of_witness]
  simp [challenge_responder_resume, project_responder_activation_result,
    project_responder_state, project_responder_phase, project_responder_pending_first,
    project_responder_pending_outgoing, challenge_first_share_of_witness]

/-- responder 输出暂存 key 的 resume 在 witness 投影下与 challenge resume 交换。 -/
theorem project_responder_resume_pending_key_of_witness
    (gen : GroupGenerator.{0}) (n : ℕ) (witness : DDHRealWitness) :
    (responder_resume gen
      { sec_param := n
        group? := some witness.G
        secret? := some witness.responder_secret
        phase := .sent_second
        pending_peer_share := none
        pending_outgoing := some (challenge_responder_key_envelope witness.to_sample) }).bind
        (fun result => PMF.pure
          (project_responder_activation_result witness.to_sample result)) =
      challenge_responder_resume witness.to_sample
        (project_responder_state witness.to_sample
          { sec_param := n
            group? := some witness.G
            secret? := some witness.responder_secret
            phase := .sent_second
            pending_peer_share := none
            pending_outgoing := some (challenge_responder_key_envelope witness.to_sample) }) := by
  simp [responder_resume, challenge_responder_resume, project_responder_activation_result,
    project_responder_state, project_responder_phase, project_responder_pending_first,
    project_responder_pending_outgoing]

noncomputable def challenge_initiator_program
    (sample : DDHSample.{0}) :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := ChallengeInitiatorState
  init := challenge_initiator_init
  receive := challenge_initiator_receive
  resume := challenge_initiator_resume sample
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def challenge_responder_program
    (sample : DDHSample.{0}) :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := ChallengeResponderState
  init := challenge_responder_init
  receive := challenge_responder_receive
  resume := challenge_responder_resume sample
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def challenge_ke_sender_machine
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    Machine SMCEasyUCPayload Unit where
  id := ke_sender_id
  communication_set :=
    { ke_sender_to_smc_sender_port
    , ke_sender_to_forw_ke_forward_port
    , ke_sender_to_forw_ke_return_port
    }
  program := challenge_initiator_program sample
  well_formed := (ke_sender_machine gen).well_formed

noncomputable def challenge_ke_receiver_machine
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    Machine SMCEasyUCPayload Unit where
  id := ke_receiver_id
  communication_set :=
    { ke_receiver_to_smc_receiver_port
    , ke_receiver_to_forw_ke_forward_port
    , ke_receiver_to_forw_ke_return_port
    }
  program := challenge_responder_program sample
  well_formed := (ke_receiver_machine gen).well_formed

noncomputable def challenge_protocol_ke_sender_machine
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    Machine.{0, 0, 1} SMCEasyUCPayload Unit :=
  lift_machine_to_type1 (challenge_ke_sender_machine gen sample)

noncomputable def challenge_protocol_ke_receiver_machine
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    Machine.{0, 0, 1} SMCEasyUCPayload Unit :=
  lift_machine_to_type1 (challenge_ke_receiver_machine gen sample)

/-- 真实 initiator 的运行时 protocol-machine state。 -/
noncomputable def real_initiator_protocol_state
    (gen : GroupGenerator.{0}) (st : InitiatorState) :
    ProtocolMachineState SMCEasyUCPayload := {
  Out := Unit
  machine := ke_sender_machine gen
  state := st
}

/-- challenge-programmed initiator 的运行时 protocol-machine state。 -/
noncomputable def challenge_initiator_protocol_state
    (gen : GroupGenerator.{0}) (sample : DDHSample.{0})
    (st : ChallengeInitiatorState) :
    ProtocolMachineState SMCEasyUCPayload := {
  Out := Unit
  machine := challenge_protocol_ke_sender_machine gen sample
  state := ⟨st⟩
}

/-- 真实 responder 的运行时 protocol-machine state。 -/
noncomputable def real_responder_protocol_state
    (gen : GroupGenerator.{0}) (st : ResponderState) :
    ProtocolMachineState SMCEasyUCPayload := {
  Out := Unit
  machine := protocol_ke_receiver_machine gen
  state := st
}

/-- challenge-programmed responder 的运行时 protocol-machine state。 -/
noncomputable def challenge_responder_protocol_state
    (gen : GroupGenerator.{0}) (sample : DDHSample.{0})
    (st : ChallengeResponderState) :
    ProtocolMachineState SMCEasyUCPayload := {
  Out := Unit
  machine := challenge_protocol_ke_receiver_machine gen sample
  state := ⟨st⟩
}

/-- 把真实 initiator protocol-machine state 投影为 challenge state。 -/
noncomputable def project_initiator_protocol_state
    (gen : GroupGenerator.{0}) (sample : DDHSample.{0})
    (st : InitiatorState) : ProtocolMachineState SMCEasyUCPayload :=
  challenge_initiator_protocol_state gen sample (project_initiator_state st)

/-- 把真实 responder protocol-machine state 投影为 challenge state。 -/
noncomputable def project_responder_protocol_state
    (gen : GroupGenerator.{0}) (sample : DDHSample.{0})
    (st : ResponderState) : ProtocolMachineState SMCEasyUCPayload :=
  challenge_responder_protocol_state gen sample (project_responder_state sample st)

noncomputable def challenge_real_machines
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    List (AnyMachine SMCEasyUCPayload) :=
  [ ⟨Unit, challenge_protocol_ke_sender_machine gen sample⟩
  , ⟨Unit, challenge_protocol_ke_receiver_machine gen sample⟩
  , ⟨Unit, forw_ke_forward_machine⟩
  , ⟨Unit, forw_ke_return_machine⟩
  ]

theorem machine_ids_challenge_real_machines
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    machine_ids (challenge_real_machines gen sample) = machine_id_list := by
  simp [challenge_real_machines, machine_ids, machine_id_list, AnyMachine.id,
    challenge_protocol_ke_sender_machine, challenge_protocol_ke_receiver_machine,
    challenge_ke_sender_machine, challenge_ke_receiver_machine,
    lift_machine_to_type1, forw_ke_forward_machine, forw_ke_return_machine, IdealForw,
    Functionality.ForwImpl.machine, forw_ke_forward_ids, forw_ke_return_ids]

theorem challenge_real_unique_ids
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    (machine_ids (challenge_real_machines gen sample)).Nodup := by
  rw [machine_ids_challenge_real_machines gen sample]
  native_decide

theorem challenge_real_caller_has_matching_subroutine
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
  ∀ m ∈ challenge_real_machines gen sample, ∀ mid : MachineId,
    is_caller_of_id m.2 mid →
      ∃ m' ∈ challenge_real_machines gen sample,
        AnyMachine.id m' = mid ∧ is_subroutine_of_id m'.2 (AnyMachine.id m) := by
  simpa [challenge_real_machines, real_machines,
    challenge_protocol_ke_sender_machine, challenge_protocol_ke_receiver_machine,
    challenge_ke_sender_machine, challenge_ke_receiver_machine,
    ke_sender_machine, protocol_ke_receiver_machine, ke_receiver_machine,
    lift_machine_to_type1] using
    (real_caller_has_matching_subroutine gen)

theorem challenge_real_subroutine_has_matching_caller
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
  ∀ m ∈ challenge_real_machines gen sample, ∀ mid : MachineId,
    is_subroutine_of_id m.2 mid →
      mid ∈ machine_ids (challenge_real_machines gen sample) →
      ∃ m' ∈ challenge_real_machines gen sample,
        AnyMachine.id m' = mid ∧ is_caller_of_id m'.2 (AnyMachine.id m) := by
  simpa [challenge_real_machines, real_machines,
    challenge_protocol_ke_sender_machine, challenge_protocol_ke_receiver_machine,
    challenge_ke_sender_machine, challenge_ke_receiver_machine,
    machine_ids_challenge_real_machines, machine_ids_real_machines,
    ke_sender_machine, protocol_ke_receiver_machine, ke_receiver_machine,
    lift_machine_to_type1] using
    (real_subroutine_has_matching_caller gen)

theorem challenge_real_env_separated
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    env_id ∉ machine_ids (challenge_real_machines gen sample) := by
  rw [machine_ids_challenge_real_machines gen sample]
  native_decide

theorem challenge_real_adv_separated
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    adv_id ∉ machine_ids (challenge_real_machines gen sample) := by
  rw [machine_ids_challenge_real_machines gen sample]
  native_decide

theorem challenge_real_no_direct_environment_communication
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    ∀ m ∈ challenge_real_machines gen sample, ∀ p ∈ m.2.communication_set,
      p.dest ≠ env_id := by
  simpa [challenge_real_machines, real_machines,
    challenge_protocol_ke_sender_machine, challenge_protocol_ke_receiver_machine,
    challenge_ke_sender_machine, challenge_ke_receiver_machine,
    ke_sender_machine, protocol_ke_receiver_machine, ke_receiver_machine,
    lift_machine_to_type1] using
    (real_no_direct_environment_communication gen)

theorem challenge_real_adversary_communication_is_backdoor
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    ∀ m ∈ challenge_real_machines gen sample, ∀ p ∈ m.2.communication_set,
      p.dest = adv_id → p.label = .backdoor := by
  simpa [challenge_real_machines, real_machines,
    challenge_protocol_ke_sender_machine, challenge_protocol_ke_receiver_machine,
    challenge_ke_sender_machine, challenge_ke_receiver_machine,
    ke_sender_machine, protocol_ke_receiver_machine, ke_receiver_machine,
    lift_machine_to_type1] using
    (real_adversary_communication_is_backdoor gen)

noncomputable def challenge_real_protocol
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    Protocol SMCEasyUCPayload where
  machines := challenge_real_machines gen sample
  corruptible_machines := ∅
  unique_ids := challenge_real_unique_ids gen sample
  caller_has_matching_subroutine :=
    challenge_real_caller_has_matching_subroutine gen sample
  subroutine_has_matching_caller :=
    challenge_real_subroutine_has_matching_caller gen sample
  env_separated := challenge_real_env_separated gen sample
  adv_separated := challenge_real_adv_separated gen sample
  no_direct_environment_communication :=
    challenge_real_no_direct_environment_communication gen sample
  adversary_communication_is_backdoor :=
    challenge_real_adversary_communication_is_backdoor gen sample

/--
challenge-programmed 真实协议在固定安全参数下的默认初始状态。

与真实协议不同，这里的两台 DHKE party 不保存 secret exponent；
DDH sample 已经被写进它们的程序闭包中。
-/
noncomputable def challenge_real_protocol_states
    (gen : GroupGenerator) (sample : DDHSample.{0}) (n : ℕ) :
    List (AnyMachineState SMCEasyUCPayload) :=
  default_machine_states (challenge_real_machines gen sample) n

/-- challenge-programmed 真实协议的 `initial_states` 展开为默认状态列表。 -/
theorem challenge_real_initial_states_eq_default
    (gen : GroupGenerator) (sample : DDHSample.{0}) (n : ℕ) :
    (challenge_real_protocol gen sample).initial_states n =
      PMF.pure (challenge_real_protocol_states gen sample n) := by
  rfl

/-- challenge protocol 与真实 DHKE protocol 有相同的 machine identity 集合。 -/
theorem challenge_real_machine_ids_eq_real
    (gen : GroupGenerator) (sample : DDHSample.{0}) :
    machine_ids (challenge_real_protocol gen sample).machines =
      machine_ids (real_protocol gen).machines := by
  simp [challenge_real_protocol, real_protocol,
    machine_ids_challenge_real_machines, machine_ids_real_machines]

/-- challenge protocol 与真实 DHKE protocol 有相同的 main-machine 判断。 -/
theorem challenge_real_is_main_machine_iff
    (gen : GroupGenerator) (sample : DDHSample.{0}) (mid : MachineId) :
    (challenge_real_protocol gen sample).is_main_machine mid ↔
      (real_protocol gen).is_main_machine mid := by
  classical
  constructor
  · intro h
    rcases h with ⟨m, hm, h_id, ext_id, _hm_ext, h_sub, h_external⟩
    simp [challenge_real_protocol, challenge_real_machines] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · refine ⟨⟨Unit, ke_sender_machine gen⟩, ?_, ?_, smc_sender_id, ?_⟩
      · simp [real_protocol, real_machines]
      · simpa [AnyMachine.id, challenge_protocol_ke_sender_machine,
          challenge_ke_sender_machine, lift_machine_to_type1, ke_sender_machine] using h_id
      · refine ⟨?_, ?_, ?_⟩
        · simp [real_protocol, real_machines]
        · refine ⟨ke_sender_to_smc_sender_port, ?_, rfl, rfl⟩
          simp [ke_sender_machine]
        · simp [real_protocol, machine_ids_real_machines, machine_id_list,
            smc_sender_ne_ke_sender,
            smc_sender_ne_ke_receiver, smc_sender_ne_forw_ke_forward,
            smc_sender_ne_forw_ke_return]
    · refine ⟨⟨Unit, protocol_ke_receiver_machine gen⟩, ?_, ?_,
        smc_receiver_id, ?_⟩
      · simp [real_protocol, real_machines]
      · simpa [AnyMachine.id, challenge_protocol_ke_receiver_machine,
          challenge_ke_receiver_machine, protocol_ke_receiver_machine,
          ke_receiver_machine, lift_machine_to_type1] using h_id
      · refine ⟨?_, ?_, ?_⟩
        · simp [real_protocol, real_machines]
        · refine ⟨ke_receiver_to_smc_receiver_port, ?_, rfl, rfl⟩
          simp [protocol_ke_receiver_machine, lift_machine_to_type1,
            ke_receiver_machine]
        · simp [real_protocol, machine_ids_real_machines, machine_id_list,
            smc_receiver_ne_ke_sender,
            smc_receiver_ne_ke_receiver, smc_receiver_ne_forw_ke_forward,
            smc_receiver_ne_forw_ke_return]
    · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
      change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
      simp [Functionality.ForwImpl.communication_set] at hp
      rcases hp with rfl | rfl | rfl
      · have h_ext : ext_id = ke_sender_id := by
          simpa [forw_ke_forward_ids, forw_sender_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [challenge_real_protocol, machine_ids_challenge_real_machines,
            machine_id_list, h_ext])
      · have h_ext : ext_id = ke_receiver_id := by
          simpa [forw_ke_forward_ids, forw_receiver_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [challenge_real_protocol, machine_ids_challenge_real_machines,
            machine_id_list, h_ext])
      · cases h_label
    · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
      change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
      simp [Functionality.ForwImpl.communication_set] at hp
      rcases hp with rfl | rfl | rfl
      · have h_ext : ext_id = ke_receiver_id := by
          simpa [forw_ke_return_ids, forw_sender_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [challenge_real_protocol, machine_ids_challenge_real_machines,
            machine_id_list, h_ext])
      · have h_ext : ext_id = ke_sender_id := by
          simpa [forw_ke_return_ids, forw_receiver_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [challenge_real_protocol, machine_ids_challenge_real_machines,
            machine_id_list, h_ext])
      · cases h_label
  · intro h
    rcases h with ⟨m, hm, h_id, ext_id, _hm_ext, h_sub, h_external⟩
    simp [real_protocol, real_machines] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · refine ⟨⟨Unit, challenge_protocol_ke_sender_machine gen sample⟩, ?_, ?_,
        smc_sender_id, ?_⟩
      · simp [challenge_real_protocol, challenge_real_machines]
      · simpa [AnyMachine.id, challenge_protocol_ke_sender_machine,
          challenge_ke_sender_machine, lift_machine_to_type1, ke_sender_machine] using h_id
      · refine ⟨?_, ?_, ?_⟩
        · simp [challenge_real_protocol, challenge_real_machines]
        · refine ⟨ke_sender_to_smc_sender_port, ?_, rfl, rfl⟩
          simp [challenge_protocol_ke_sender_machine, challenge_ke_sender_machine,
            lift_machine_to_type1]
        · simp [challenge_real_protocol, machine_ids_challenge_real_machines,
            machine_id_list, smc_sender_ne_ke_sender,
            smc_sender_ne_ke_receiver, smc_sender_ne_forw_ke_forward,
            smc_sender_ne_forw_ke_return]
    · refine ⟨⟨Unit, challenge_protocol_ke_receiver_machine gen sample⟩, ?_, ?_,
        smc_receiver_id, ?_⟩
      · simp [challenge_real_protocol, challenge_real_machines]
      · simpa [AnyMachine.id, challenge_protocol_ke_receiver_machine,
          challenge_ke_receiver_machine, protocol_ke_receiver_machine,
          ke_receiver_machine, lift_machine_to_type1] using h_id
      · refine ⟨?_, ?_, ?_⟩
        · simp [challenge_real_protocol, challenge_real_machines]
        · refine ⟨ke_receiver_to_smc_receiver_port, ?_, rfl, rfl⟩
          simp [challenge_protocol_ke_receiver_machine,
            challenge_ke_receiver_machine, lift_machine_to_type1]
        · simp [challenge_real_protocol, machine_ids_challenge_real_machines,
            machine_id_list, smc_receiver_ne_ke_sender,
            smc_receiver_ne_ke_receiver, smc_receiver_ne_forw_ke_forward,
            smc_receiver_ne_forw_ke_return]
    · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
      change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
      simp [Functionality.ForwImpl.communication_set] at hp
      rcases hp with rfl | rfl | rfl
      · have h_ext : ext_id = ke_sender_id := by
          simpa [forw_ke_forward_ids, forw_sender_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [real_protocol, machine_ids_real_machines, machine_id_list, h_ext])
      · have h_ext : ext_id = ke_receiver_id := by
          simpa [forw_ke_forward_ids, forw_receiver_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [real_protocol, machine_ids_real_machines, machine_id_list, h_ext])
      · cases h_label
    · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
      change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
      simp [Functionality.ForwImpl.communication_set] at hp
      rcases hp with rfl | rfl | rfl
      · have h_ext : ext_id = ke_receiver_id := by
          simpa [forw_ke_return_ids, forw_sender_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [real_protocol, machine_ids_real_machines, machine_id_list, h_ext])
      · have h_ext : ext_id = ke_sender_id := by
          simpa [forw_ke_return_ids, forw_receiver_port] using h_dest.symm
        subst ext_id
        exfalso
        exact h_external (by
          simp [real_protocol, machine_ids_real_machines, machine_id_list, h_ext])
      · cases h_label

/-- challenge protocol 与真实 DHKE protocol 有相同的 internal-machine 判断。 -/
theorem challenge_real_is_internal_machine_iff
    (gen : GroupGenerator) (sample : DDHSample.{0}) (mid : MachineId) :
    (challenge_real_protocol gen sample).is_internal_machine mid ↔
      (real_protocol gen).is_internal_machine mid := by
  classical
  simp [Protocol.is_internal_machine, Protocol.has_machine_id,
    challenge_real_is_main_machine_iff gen sample mid,
    challenge_real_machine_ids_eq_real gen sample]

/--
把真实 DHKE setup 搬到 DDH challenge-programmed protocol。

该转换只替换 protocol machine 的程序；machine id、端口、main/internal 角色和
environment/adversary 约束保持不变。
-/
noncomputable def challenge_real_setup_of_real_setup
    (gen : GroupGenerator) (sample : DDHSample.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    ExecutionSetup (challenge_real_protocol gen sample) A E where
  corrupted_parties := real_setup.corrupted_parties
  env_port_policy_holds := by
    intro p hp
    rcases real_setup.env_port_policy_holds p hp with h_backdoor | h_input
    · exact Or.inl h_backdoor
    · rcases h_input with ⟨h_not_adv, h_label, h_main⟩
      exact Or.inr ⟨h_not_adv, h_label,
        (challenge_real_is_main_machine_iff gen sample p.dest).2 h_main⟩
  corruption_allowed := by
    intro mid h_mid
    exact real_setup.corruption_allowed h_mid
  adv_port_destinations_restricted :=
    real_setup.adv_port_destinations_restricted

/--
把标准 ideal KE setup 搬到 DDH challenge-programmed ideal protocol。

该转换把 IdealKE 的 key sampler 固定为 challenge 样本的 key component，并把
simulator 替换为同一 challenge 样本编程出的 simulator。Dummy parties、
environment 以及显式 control/backdoor 接口保持不变。
-/
noncomputable def challenge_ideal_setup_of_ideal_setup
    (gen : GroupGenerator.{0}) (sample : DDHSample.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) :
    ExecutionSetup (challenge_ideal_protocol gen sample)
      (challenge_simulator gen sample A) E where
  corrupted_parties := ideal_setup.corrupted_parties
  env_port_policy_holds := by
    intro p hp
    rcases ideal_setup.env_port_policy_holds p hp with h_backdoor | h_input
    · exact Or.inl h_backdoor
    · rcases h_input with ⟨h_not_adv, h_label, h_main⟩
      exact Or.inr ⟨h_not_adv, h_label,
        (challenge_ideal_is_main_machine_iff gen sample p.dest).2 h_main⟩
  corruption_allowed := by
    intro mid h_mid
    exact ideal_setup.corruption_allowed h_mid
  adv_port_destinations_restricted := by
    intro p hp
    simp [challenge_simulator, simulator_machine, simulator_to_environment_port] at hp
    rcases hp with rfl
    rfl

/-! ## Controller-level executions -/

/--
一次完整 controller execution 的打包形式。

`ExecutionSetup` 的类型依赖 protocol、adversary 和 environment；在 reduction
里它们可能由 DDH challenge 决定，所以这里显式打包四者。
-/
structure ControllerExecution (Payload : Type) where
  protocol : Protocol Payload
  adversary : Adversary Payload
  environment : Environment Payload
  setup : ExecutionSetup protocol adversary environment

namespace ControllerExecution

/-- 运行一个已打包的 controller execution。 -/
noncomputable def exec {Payload : Type}
    (execution : ControllerExecution Payload) : Ensemble Bool :=
  Controller.exec execution.setup

/-- 在给定 protocol 初始状态列表时运行一个已打包的 controller execution。 -/
noncomputable def exec_with_protocol_states {Payload : Type}
    (execution : ControllerExecution Payload) (n : ℕ)
    (protocol_states : List (AnyMachineState Payload)) : PMF Bool :=
  (Controller.run_steps execution.setup LeanCryptoProtocols.max_controller_steps
      (Controller.initial_state_with_protocol_states
        execution.setup n protocol_states)).bind fun st =>
    PMF.pure (Controller.environment_output st)

/-- `exec` 先采样 protocol initial states，再运行固定初始状态的 controller。 -/
theorem exec_eq_bind_initial_states {Payload : Type}
    (execution : ControllerExecution Payload) (n : ℕ) :
    exec execution n =
      (execution.protocol.initial_states n).bind fun protocol_states =>
        exec_with_protocol_states execution n protocol_states := by
  rfl

end ControllerExecution

/--
由真实 DHKE setup 和 DDH challenge 构造完整 controller execution。

这是 reduction 实际需要的 controller-level 对象：adversary 与 environment
来自真实执行；protocol 程序被 DDH sample 编程；setup 由真实 setup 的结构证明
搬运而来。
-/
noncomputable def challenge_execution_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (sample : DDHSample.{0}) :
    ControllerExecution SMCEasyUCPayload where
  protocol := challenge_real_protocol gen sample
  adversary := A
  environment := E
  setup := challenge_real_setup_of_real_setup gen sample real_setup

/--
由标准 ideal KE setup 和 DDH challenge 构造 challenge-programmed ideal
controller execution。

这里 adversary 被替换为 `challenge_simulator gen sample A`，用于把当前 DDH
sample 的 `X,Y` 伪造成真实世界 forwarding observations；IdealKE 只接收当前
DDH sample 的 key component。
-/
noncomputable def challenge_ideal_execution_of_ideal_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E)
    (sample : DDHSample.{0}) :
    ControllerExecution SMCEasyUCPayload where
  protocol := challenge_ideal_protocol gen sample
  adversary := challenge_simulator gen sample A
  environment := E
  setup := challenge_ideal_setup_of_ideal_setup gen sample ideal_setup

/-- 用真实 setup 和 DDH challenge 实例化 controller，并取环境输出分布。 -/
noncomputable def challenge_controller_output_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (sample : DDHSample.{0}) : Ensemble Bool :=
  ControllerExecution.exec (challenge_execution_of_real_setup gen real_setup sample)

/--
固定 DDH sample 后，challenge-programmed 真实执行可展开为：
先使用 challenge protocol 的默认初始状态列表，再运行 controller。
-/
theorem challenge_controller_output_of_real_setup_eq_default_states
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (sample : DDHSample.{0}) :
    challenge_controller_output_of_real_setup gen real_setup sample =
      fun n =>
        ControllerExecution.exec_with_protocol_states
          (challenge_execution_of_real_setup gen real_setup sample)
          n
          (challenge_real_protocol_states gen sample n) := by
  funext n
  simp [challenge_controller_output_of_real_setup, ControllerExecution.exec,
    Controller.exec, challenge_execution_of_real_setup, challenge_real_protocol,
    challenge_real_protocol_states,
    ControllerExecution.exec_with_protocol_states]

/-- 用 ideal setup 和 DDH challenge 实例化 controller，并取环境输出分布。 -/
noncomputable def challenge_controller_output_of_ideal_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E)
    (sample : DDHSample.{0}) : Ensemble Bool :=
  ControllerExecution.exec (challenge_ideal_execution_of_ideal_setup gen ideal_setup sample)

/--
在固定 witness 初始化的真实 protocol states 上运行真实 controller。

这是把标准 `Controller.exec real_setup` 展开为 witness-coupled trace 证明时使用的
入口；它仍运行真实 protocol，而不是 challenge-programmed protocol。
-/
noncomputable def real_controller_output_of_witness
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (witness : DDHRealWitness) : Ensemble Bool :=
  fun n =>
    ControllerExecution.exec_with_protocol_states
      { protocol := real_protocol gen
        adversary := A
        environment := E
        setup := real_setup }
      n
      (real_protocol_states_of_witness gen n witness)

/--
真实 controller execution 等于先采样 DH witness，再在该 witness 给出的初始状态上
运行 controller。
-/
theorem controller_exec_real_eq_real_witness_controller_output
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    Controller.exec real_setup =
      fun n =>
        (ddh_real_witness gen n).bind fun witness =>
          real_controller_output_of_witness gen real_setup witness n := by
  funext n
  simp [Controller.exec, real_protocol, real_initial_states,
    real_controller_output_of_witness,
    ControllerExecution.exec_with_protocol_states, PMF.bind_bind]

/-- 由真实 setup 诱导出的 DDH distinguisher。 -/
noncomputable def ddh_adversary_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    Distinguisher DDHSample.{0} where
  run := fun sample n =>
    challenge_controller_output_of_real_setup gen real_setup sample n

/-- 由 ideal setup 诱导出的 DDH distinguisher。 -/
noncomputable def ddh_adversary_of_ideal_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) :
    Distinguisher DDHSample.{0} where
  run := fun sample n =>
    challenge_controller_output_of_ideal_setup gen ideal_setup sample n

/-- 真实 DDH challenge 编程后的 controller experiment。 -/
noncomputable def real_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) : Ensemble Bool :=
  fun n =>
    (ddh_real gen n).bind fun sample =>
      challenge_controller_output_of_real_setup gen real_setup sample n

/--
带 exponent witness 的真实 challenge experiment。

这个分布显式保留真实 DH party 初始化需要的 `a,b`，但 controller 侧只读取其
投影出的标准 DDH sample。后续做真实执行 trace 对齐时，可以在同一个 witness
上同时初始化真实 party 和 challenge-programmed protocol。
-/
noncomputable def real_witness_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) : Ensemble Bool :=
  fun n =>
    (ddh_real_witness gen n).bind fun witness =>
      challenge_controller_output_of_real_setup gen real_setup witness.to_sample n

/--
带 exponent witness 的 challenge experiment 投影后就是标准 DDH-real challenge
experiment。
-/
theorem real_witness_challenge_execution_eq_real_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    real_witness_challenge_execution gen real_setup =
      real_challenge_execution gen real_setup := by
  funext n
  rw [real_witness_challenge_execution, real_challenge_execution,
    ← ddh_real_witness_to_sample_eq_ddh_real gen n]
  simp [PMF.bind_bind]

/-- 随机 DDH challenge 编程后的 controller experiment。 -/
noncomputable def random_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) : Ensemble Bool :=
  fun n =>
    (ddh_random gen n).bind fun sample =>
      challenge_controller_output_of_real_setup gen real_setup sample n

/-- 随机 DDH challenge 编程后的 ideal controller experiment。 -/
noncomputable def random_ideal_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) : Ensemble Bool :=
  fun n =>
    (ddh_random gen n).bind fun sample =>
      challenge_controller_output_of_ideal_setup gen ideal_setup sample n

/-- DDH reduction 的两个游戏输出分布。 -/
noncomputable def ddh_game_one_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) : Ensemble Bool :=
  fun n => DistOutput (ddh_adversary_of_real_setup gen real_setup) (ddh_real gen) n

/-- DDH reduction 的随机游戏输出分布。 -/
noncomputable def ddh_game_two_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) : Ensemble Bool :=
  fun n => DistOutput (ddh_adversary_of_real_setup gen real_setup) (ddh_random gen) n

/-- ideal setup 对应 DDH distinguisher 的真实游戏输出分布。 -/
noncomputable def ddh_game_one_of_ideal_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) : Ensemble Bool :=
  fun n => DistOutput (ddh_adversary_of_ideal_setup gen ideal_setup) (ddh_real gen) n

/-- ideal setup 对应 DDH distinguisher 的随机游戏输出分布。 -/
noncomputable def ddh_game_two_of_ideal_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) : Ensemble Bool :=
  fun n => DistOutput (ddh_adversary_of_ideal_setup gen ideal_setup) (ddh_random gen) n

/-- setup-specific concrete challenge execution difference。 -/
noncomputable def challenge_exec_diff
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (n : ℕ) : ℝ :=
  |probTrue (real_challenge_execution gen real_setup n) -
    probTrue (random_challenge_execution gen real_setup n)|

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

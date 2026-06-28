import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.CertificateProofs

/-!
# DHKE 子证明的审计对象

本目录把 EasyUC SMC 证明中用到的 key exchange 步骤单独列出。
真实世界只包含两个 KE party 和两个 one-shot `Forw` 功能机；
理想世界直接使用通用 `IdealKE`，再由 `mk_ideal_protocol` 生成 dummy parties。
-/

set_option linter.flexible false
set_option linter.style.nativeDecide false

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Assumptions
open LeanCryptoProtocols.CaseStudy.SMCEasyUC

/-! ## DHKE identities -/

/-- DHKE 理想世界中 `IdealKE` 功能机的固定 identity。 -/
def ideal_ke_id : MachineId := 20

theorem ke_sender_ne_ideal_ke :
    ke_sender_id ≠ ideal_ke_id := by decide

theorem ke_receiver_ne_ideal_ke :
    ke_receiver_id ≠ ideal_ke_id := by decide

theorem smc_sender_ne_ideal_ke :
    smc_sender_id ≠ ideal_ke_id := by decide

theorem smc_receiver_ne_ideal_ke :
    smc_receiver_id ≠ ideal_ke_id := by decide

theorem ideal_ke_separated :
    ideal_ke_id ≠ env_id ∧ ideal_ke_id ≠ adv_id := by decide

/-- 真实 DHKE protocol 中的 machine identities。 -/
def machine_id_list : List MachineId :=
  [ke_sender_id, ke_receiver_id, forw_ke_forward_id, forw_ke_return_id]

/-- DHKE 理想功能使用的随机 key 分布：在固定群中采样 `c`，输出 `g^c`。 -/
noncomputable def sample_shared_key
    (G : GroupDescription.{0}) (_n : ℕ) : PMF SharedKey :=
  G.sample_exponent.bind fun c =>
    PMF.pure ⟨G.encode (G.pow G.generator c)⟩

/--
DHKE 理想功能使用的 key-only sampler。

理想功能只采样最终交给 dummy parties 的 key。DH public shares 不是理想功能
状态的一部分，而是由 simulator 负责模拟。
-/
noncomputable def sample_ideal_ke_key
    (G : GroupDescription.{0}) (n : ℕ) : PMF KEIdealKeyMaterial :=
  (sample_shared_key G n).bind fun shared_key =>
    PMF.pure { shared_key := shared_key }

/-- `sample_ideal_ke_key` 正是 `sample_shared_key` 的 key-only 包装。 -/
theorem sample_ideal_ke_key_eq_sample_shared_key
    (G : GroupDescription.{0}) (n : ℕ) :
    sample_ideal_ke_key G n =
      (sample_shared_key G n).bind fun shared_key =>
        PMF.pure { shared_key := shared_key } := by
  rfl

/-- DDH-random 的 key component 投影，用于 corrected challenge-ideal coupling。 -/
noncomputable def sample_ddh_random_key
    (G : GroupDescription.{0}) (n : ℕ) : PMF KEIdealKeyMaterial :=
  (ddh_random G n).bind fun sample =>
    PMF.pure { shared_key := ⟨G.encode sample.gz⟩ }

/--
DDH-random challenge 的 key component 边缘分布等于 IdealKE 的 key-only sampler。

这只是采样分布的边缘化：`ddh_random` 中额外采样的两次 public share 指数
在 key 投影下被忽略。
-/
theorem sample_ddh_random_key_eq_sample_ideal_ke_key
    (G : GroupDescription.{0}) (n : ℕ) :
    sample_ddh_random_key G n = sample_ideal_ke_key G n := by
  simp [sample_ddh_random_key, sample_ideal_ke_key, sample_shared_key,
    ddh_random, PMF.bind_bind]

/-- DDH-real 的 key component 投影。 -/
noncomputable def sample_ddh_real_key
    (G : GroupDescription.{0}) (n : ℕ) : PMF KEIdealKeyMaterial :=
  (ddh_real G n).bind fun sample =>
    PMF.pure { shared_key := ⟨G.encode sample.gz⟩ }

/-! ## Real DHKE local programs -/

/--
证明真实 DHKE 与 DDH-real game 等价时使用的 witness sample。

标准 DDH distinguisher 只能看到 `to_sample` 中的群元素；
证明中额外保留 `a,b`，以便后续对 protocol 执行与 DDH game 进行耦合。
该 witness 不参与 protocol 初始化；真实 machines 在每次会话中自行采样指数。
-/
structure DDHRealWitness (G : GroupDescription.{0}) where
  initiator_exponent : G.Exponent
  responder_exponent : G.Exponent

namespace DDHRealWitness

/-- witness 投影成标准 DDH-real sample。 -/
def to_sample {G : GroupDescription.{0}} (w : DDHRealWitness G) : DDHChallenge G :=
  { gx := G.pow G.generator w.initiator_exponent
    gy := G.pow G.generator w.responder_exponent
    gz := G.pow G.generator
      (G.mul_exp w.initiator_exponent w.responder_exponent) }

/-- witness 中 initiator 的真实本地 secret。 -/
def initiator_secret {G : GroupDescription.{0}}
    (w : DDHRealWitness G) : DHSecret G :=
  { exponent := w.initiator_exponent
    public_share :=
      ⟨G.encode (G.pow G.generator w.initiator_exponent)⟩ }

/-- witness 中 responder 的真实本地 secret。 -/
def responder_secret {G : GroupDescription.{0}}
    (w : DDHRealWitness G) : DHSecret G :=
  { exponent := w.responder_exponent
    public_share :=
      ⟨G.encode (G.pow G.generator w.responder_exponent)⟩ }

end DDHRealWitness

/-- 采样带 exponent witness 的 DDH-real 实验。 -/
noncomputable def ddh_real_witness
    (G : GroupDescription.{0}) (_n : ℕ) : PMF (DDHRealWitness G) :=
  G.sample_exponent.bind fun a =>
    G.sample_exponent.bind fun b =>
      PMF.pure {
        initiator_exponent := a
        responder_exponent := b
      }

/-- `ddh_real_witness` 投影后就是标准 DDH-real 分布。 -/
theorem ddh_real_witness_to_sample_eq_ddh_real
    (G : GroupDescription.{0}) (n : ℕ) :
    (ddh_real_witness G n).bind
        (fun w => PMF.pure w.to_sample) =
      ddh_real G n := by
  simp [ddh_real_witness, DDHRealWitness.to_sample, ddh_real,
    PMF.bind_bind]

inductive InitiatorAction where
  | send_first
  | output_key (peer_share : GroupElement)

inductive InitiatorPhase where
  | waiting_init
  | waiting_second
  | done

inductive ResponderPhase where
  | waiting_first
  | sent_second
  | done

structure InitiatorState (G : GroupDescription.{0}) where
  secret? : Option (DHSecret G)
  phase : InitiatorPhase
  pending_action : Option InitiatorAction

structure ResponderState (G : GroupDescription.{0}) where
  secret? : Option (DHSecret G)
  phase : ResponderPhase
  pending_peer_share : Option GroupElement
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

def initiator_init (G : GroupDescription.{0}) (_n : ℕ) : InitiatorState G := {
  secret? := none
  phase := .waiting_init
  pending_action := none
}

def responder_init (G : GroupDescription.{0}) (_n : ℕ) : ResponderState G := {
  secret? := none
  phase := .waiting_first
  pending_peer_share := none
  pending_outgoing := none
}

def initiator_key_envelope
    (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := ke_sender_to_smc_sender_port
    message := {
      label := .subroutineOutput
      payload := .ke (.key shared_key)
    }
    label_matches := rfl
  }

def responder_key_envelope
    (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := ke_receiver_to_smc_receiver_port
    message := {
      label := .subroutineOutput
      payload := .ke (.key shared_key)
    }
    label_matches := rfl
  }

def initiator_receive {G : GroupDescription.{0}} (st : InitiatorState G)
    (msg : Message SMCEasyUCPayload) :
    InitiatorState G :=
  match st.phase, msg.label, msg.payload with
  | .waiting_init, .input, .ke .init =>
      { st with
        phase := .waiting_second
        pending_action := some .send_first }
  | .waiting_second, .subroutineOutput,
      .forw (.delivered _ _ (.ke_second share)) =>
      { st with pending_action := some (.output_key share) }
  | _, _, _ =>
      st

def responder_receive {G : GroupDescription.{0}} (st : ResponderState G)
    (msg : Message SMCEasyUCPayload) :
    ResponderState G :=
  match st.phase, msg.label, msg.payload with
  | .waiting_first, .subroutineOutput,
      .forw (.delivered _ _ (.ke_first share)) =>
      { st with pending_peer_share := some share }
  | _, _, _ =>
      st

noncomputable def initiator_resume
    (G : GroupDescription.{0})
    (st : InitiatorState G) :
    PMF (ActivationResult SMCEasyUCPayload (InitiatorState G)) :=
  match st.pending_action with
  | none =>
      PMF.pure {
        state := st
        outgoing? := none
      }
  | some .send_first =>
      (match st.secret? with
        | some secret => PMF.pure secret
        | none => sample_dh_secret G).bind fun secret =>
        PMF.pure {
          state := {
            st with
              secret? := some secret
              phase := .waiting_second
              pending_action := none
          }
          outgoing? := some {
            port := ke_sender_to_forw_ke_forward_port
            message := {
              label := .input
              payload := .forw
                (.submit ke_sender_id ke_receiver_id (.ke_first secret.public_share))
            }
            label_matches := rfl
          }
        }
  | some (.output_key peer_share) =>
      let shared_key :=
        match st.secret? with
        | some secret => derive_key_from_secret secret peer_share
        | none => default_shared_key
      PMF.pure {
        state := {
          st with
            secret? := none
            phase := .done
            pending_action := none
        }
        outgoing? := some (initiator_key_envelope shared_key)
      }

noncomputable def responder_resume
    (G : GroupDescription.{0})
    (st : ResponderState G) :
    PMF (ActivationResult SMCEasyUCPayload (ResponderState G)) :=
  match st.pending_outgoing with
  | some env =>
      PMF.pure {
        state := { st with pending_outgoing := none, phase := .done }
        outgoing? := some env
      }
  | none =>
      match st.pending_peer_share with
      | none =>
          PMF.pure {
            state := st
            outgoing? := none
          }
      | some peer_share =>
          (match st.secret? with
            | some secret => PMF.pure secret
            | none => sample_dh_secret G).bind fun secret =>
            let shared_key := derive_key_from_secret secret peer_share
            PMF.pure {
              state := {
                st with
                  pending_peer_share := none
                  secret? := some secret
                  phase := .sent_second
                  pending_outgoing := some (responder_key_envelope shared_key)
              }
              outgoing? := some {
                port := ke_receiver_to_forw_ke_return_port
                message := {
                  label := .input
                  payload := .forw
                    (.submit ke_receiver_id ke_sender_id
                      (.ke_second secret.public_share))
                }
                label_matches := rfl
              }
            }

noncomputable def initiator_program
    (G : GroupDescription.{0}) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := InitiatorState G
  init := initiator_init G
  activate := fun st incoming? =>
    let st' :=
      match incoming? with
      | none => st
      | some msg =>
          match st.phase, msg.label, msg.payload with
          | .waiting_init, .input, .ke .init =>
              { st with
                phase := .waiting_second
                pending_action := some .send_first }
          | .waiting_second, .subroutineOutput,
              .forw (.delivered _ _ (.ke_second share)) =>
              { st with pending_action := some (.output_key share) }
          | _, _, _ =>
              st
    match st'.pending_action with
    | none =>
        PMF.pure {
          state := st'
          outgoing? := none
        }
    | some .send_first =>
        (match st'.secret? with
          | some secret => PMF.pure secret
          | none => sample_dh_secret G).bind fun secret =>
          PMF.pure {
            state := {
              st' with
                secret? := some secret
                phase := .waiting_second
                pending_action := none
            }
            outgoing? := some {
              port := ke_sender_to_forw_ke_forward_port
              message := {
                label := .input
                payload := .forw
                  (.submit ke_sender_id ke_receiver_id (.ke_first secret.public_share))
              }
              label_matches := rfl
            }
          }
    | some (.output_key peer_share) =>
        let shared_key :=
          match st'.secret? with
          | some secret => derive_key_from_secret secret peer_share
          | none => default_shared_key
        PMF.pure {
          state := {
            st' with
              secret? := none
              phase := .done
              pending_action := none
          }
          outgoing? := some (initiator_key_envelope shared_key)
        }
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def responder_program
    (G : GroupDescription.{0}) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := ResponderState G
  init := responder_init G
  activate := fun st incoming? =>
    let st' :=
      match incoming? with
      | none => st
      | some msg =>
          match st.phase, msg.label, msg.payload with
          | .waiting_first, .subroutineOutput,
              .forw (.delivered _ _ (.ke_first share)) =>
              { st with pending_peer_share := some share }
          | _, _, _ =>
              st
    match st'.pending_outgoing with
    | some env =>
        PMF.pure {
          state := { st' with pending_outgoing := none, phase := .done }
          outgoing? := some env
        }
    | none =>
        match st'.pending_peer_share with
        | none =>
            PMF.pure {
              state := st'
              outgoing? := none
            }
        | some peer_share =>
            (match st'.secret? with
              | some secret => PMF.pure secret
              | none => sample_dh_secret G).bind fun secret =>
              let shared_key := derive_key_from_secret secret peer_share
              PMF.pure {
                state := {
                  st' with
                    pending_peer_share := none
                    secret? := some secret
                    phase := .sent_second
                    pending_outgoing := some (responder_key_envelope shared_key)
                }
                outgoing? := some {
                  port := ke_receiver_to_forw_ke_return_port
                  message := {
                    label := .input
                    payload := .forw
                      (.submit ke_receiver_id ke_sender_id
                        (.ke_second secret.public_share))
                  }
                  label_matches := rfl
                }
              }
  is_halted := fun _ => false
  output := fun _ => ()

/--
DHKE 这一步的理想 KE 功能机。

Dummy party ids 仍然是两个 KE party；external identities 是它们在外层 SMC
协议中的 caller，也就是 `smc_sender_id` 与 `smc_receiver_id`。
-/
noncomputable def ideal_ke_ids (G : GroupDescription.{0}) : KEIds where
  initiator_id := ke_sender_id
  responder_id := ke_receiver_id
  functionality_id := ideal_ke_id
  initiator_external_id := smc_sender_id
  responder_external_id := smc_receiver_id
  initiator_ne_responder := ke_sender_ne_ke_receiver
  initiator_ne_functionality := ke_sender_ne_ideal_ke
  responder_ne_functionality := ke_receiver_ne_ideal_ke
  initiator_id_separated := ke_sender_separated
  responder_id_separated := ke_receiver_separated
  functionality_separated := ideal_ke_separated
  initiator_external_separated :=
    ⟨smc_sender_ne_ke_sender, smc_sender_ne_ke_receiver,
      smc_sender_ne_ideal_ke, smc_sender_separated.1,
      smc_sender_separated.2⟩
  responder_external_separated :=
    ⟨smc_receiver_ne_ke_sender, smc_receiver_ne_ke_receiver,
      smc_receiver_ne_ideal_ke, smc_receiver_separated.1,
      smc_receiver_separated.2⟩
  sample_key_material := sample_ideal_ke_key G

/-- DHKE 子证明的目标理想功能。 -/
noncomputable def ideal_ke_functionality
    (G : GroupDescription.{0}) :
    IdealFunctionality SMCEasyUCPayload :=
  IdealKE (ideal_ke_ids G)

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

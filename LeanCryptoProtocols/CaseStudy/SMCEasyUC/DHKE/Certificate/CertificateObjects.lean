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

/-- DHKE 理想功能使用的随机 key 分布：采样群、采样指数，输出 `g^c` 的编码。 -/
noncomputable def sample_shared_key
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF SharedKey :=
  (gen n).bind fun G =>
    G.sample_exponent.bind fun c =>
      PMF.pure ⟨G.encode (G.pow G.generator c)⟩

/--
DHKE 理想功能使用的 key-only sampler。

理想功能只采样最终交给 dummy parties 的 key。DH public shares 不是理想功能
状态的一部分，而是由 simulator 负责模拟。
-/
noncomputable def sample_ideal_ke_key
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF KEIdealKeyMaterial :=
  (sample_shared_key gen n).bind fun shared_key =>
    PMF.pure { shared_key := shared_key }

/-- `sample_ideal_ke_key` 正是 `sample_shared_key` 的 key-only 包装。 -/
theorem sample_ideal_ke_key_eq_sample_shared_key
    (gen : GroupGenerator.{0}) (n : ℕ) :
    sample_ideal_ke_key gen n =
      (sample_shared_key gen n).bind fun shared_key =>
        PMF.pure { shared_key := shared_key } := by
  rfl

/-- DDH-random 的 key component 投影，用于 corrected challenge-ideal coupling。 -/
noncomputable def sample_ddh_random_key
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF KEIdealKeyMaterial :=
  (ddh_random gen n).bind fun sample =>
    PMF.pure { shared_key := ⟨sample.1.encode sample.2.gz⟩ }

/--
DDH-random challenge 的 key component 边缘分布等于 IdealKE 的 key-only sampler。

这只是采样分布的边缘化：`ddh_random` 中额外采样的两次 public share 指数
在 key 投影下被忽略。
-/
theorem sample_ddh_random_key_eq_sample_ideal_ke_key
    (gen : GroupGenerator.{0}) (n : ℕ) :
    sample_ddh_random_key gen n = sample_ideal_ke_key gen n := by
  simp [sample_ddh_random_key, sample_ideal_ke_key, sample_shared_key,
    ddh_random, PMF.bind_bind]

/-- DDH-real 的 key component 投影。 -/
noncomputable def sample_ddh_real_key
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF KEIdealKeyMaterial :=
  (ddh_real gen n).bind fun sample =>
    PMF.pure { shared_key := ⟨sample.1.encode sample.2.gz⟩ }

/-! ## Real DHKE local programs -/

/-- 真实 DH party 的本地 secret：群描述、指数和公开 share。 -/
structure DHSecret where
  G : GroupDescription.{0}
  exponent : G.Exponent
  public_share : GroupElement

/--
证明真实 DHKE 与 DDH-real game 等价时使用的 witness sample。

标准 DDH distinguisher 只能看到 `to_sample` 中的群元素；
证明中额外保留 `a,b`，用于初始化真实 party 的本地 secret exponent。
-/
structure DDHRealWitness where
  G : GroupDescription.{0}
  initiator_exponent : G.Exponent
  responder_exponent : G.Exponent

namespace DDHRealWitness

/-- witness 投影成标准 DDH-real sample。 -/
def to_sample (w : DDHRealWitness) : DDHSample.{0} :=
  ⟨w.G,
    { gx := w.G.pow w.G.generator w.initiator_exponent
      gy := w.G.pow w.G.generator w.responder_exponent
      gz := w.G.pow w.G.generator
        (w.G.mul_exp w.initiator_exponent w.responder_exponent) }⟩

/-- witness 中 initiator 的真实本地 secret。 -/
def initiator_secret (w : DDHRealWitness) : DHSecret :=
  { G := w.G
    exponent := w.initiator_exponent
    public_share :=
      ⟨w.G.encode (w.G.pow w.G.generator w.initiator_exponent)⟩ }

/-- witness 中 responder 的真实本地 secret。 -/
def responder_secret (w : DDHRealWitness) : DHSecret :=
  { G := w.G
    exponent := w.responder_exponent
    public_share :=
      ⟨w.G.encode (w.G.pow w.G.generator w.responder_exponent)⟩ }

end DDHRealWitness

/-- 采样带 exponent witness 的 DDH-real 实验。 -/
noncomputable def ddh_real_witness
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF DDHRealWitness :=
  (gen n).bind fun G =>
    G.sample_exponent.bind fun a =>
      G.sample_exponent.bind fun b =>
        PMF.pure {
          G := G
          initiator_exponent := a
          responder_exponent := b
        }

/-- `ddh_real_witness` 投影后就是标准 DDH-real 分布。 -/
theorem ddh_real_witness_to_sample_eq_ddh_real
    (gen : GroupGenerator.{0}) (n : ℕ) :
    (ddh_real_witness gen n).bind
        (fun w => PMF.pure w.to_sample) =
      ddh_real gen n := by
  simp [ddh_real_witness, DDHRealWitness.to_sample, ddh_real,
    PMF.bind_bind]

/-- 采样 secret exponent `a` 并给出公开 share `g^a`。 -/
noncomputable def sample_dh_secret
    (gen : GroupGenerator.{0}) (n : ℕ) : PMF DHSecret :=
  (gen n).bind fun G =>
    G.sample_exponent.bind fun a =>
      PMF.pure {
        G := G
        exponent := a
        public_share := ⟨G.encode (G.pow G.generator a)⟩
      }

/-- 在已经公开固定的群描述 `G` 中采样 secret exponent 与公开 share。 -/
noncomputable def sample_dh_secret_in_group
    (G : GroupDescription.{0}) : PMF DHSecret :=
  G.sample_exponent.bind fun a =>
    PMF.pure {
      G := G
      exponent := a
      public_share := ⟨G.encode (G.pow G.generator a)⟩
    }

/-- 用本地 secret exponent 和对方公开 share 计算 DH key。 -/
def derive_key_from_secret
    (secret : DHSecret) (peer_share : GroupElement) : SharedKey :=
  match secret.G.decode peer_share.value with
  | some peer_element =>
      ⟨secret.G.encode (secret.G.pow peer_element secret.exponent)⟩
  | none =>
      default_shared_key

/--
在同一个群描述 `G` 下，持有 exponent `a` 的一方收到 `g^b` 后，
`derive_key_from_secret` 得到的 key 正是 `g^(ab)` 的编码。
-/
theorem derive_key_from_secret_generator
    (G : GroupDescription.{0}) (a b : G.Exponent) :
    derive_key_from_secret
        { G := G
          exponent := a
          public_share := ⟨G.encode (G.pow G.generator a)⟩ }
        ⟨G.encode (G.pow G.generator b)⟩ =
      ⟨G.encode (G.pow G.generator (G.mul_exp a b))⟩ := by
  simp [derive_key_from_secret, G.decode_encode]
  rw [← G.pow_mul_generator_comm a b, G.pow_mul_generator]

/--
在同一个群描述 `G` 下，双方分别持有 `a` 和 `b` 时，
从对方公开 share 计算出的 DH key 相同。
-/
theorem derive_key_from_secret_comm
    (G : GroupDescription.{0}) (a b : G.Exponent) :
    derive_key_from_secret
        { G := G
          exponent := a
          public_share := ⟨G.encode (G.pow G.generator a)⟩ }
        ⟨G.encode (G.pow G.generator b)⟩ =
      derive_key_from_secret
        { G := G
          exponent := b
          public_share := ⟨G.encode (G.pow G.generator b)⟩ }
        ⟨G.encode (G.pow G.generator a)⟩ := by
  simp [derive_key_from_secret, G.decode_encode]
  exact congrArg G.encode (G.pow_mul_generator_comm a b).symm

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

structure InitiatorState where
  sec_param : ℕ
  group? : Option GroupDescription.{0}
  secret? : Option DHSecret
  phase : InitiatorPhase
  pending_action : Option InitiatorAction

structure ResponderState where
  sec_param : ℕ
  group? : Option GroupDescription.{0}
  secret? : Option DHSecret
  phase : ResponderPhase
  pending_peer_share : Option GroupElement
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

def initiator_init (n : ℕ) : InitiatorState := {
  sec_param := n
  group? := none
  secret? := none
  phase := .waiting_init
  pending_action := none
}

def responder_init (n : ℕ) : ResponderState := {
  sec_param := n
  group? := none
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
      source := some ke_sender_id
      label := .subroutineOutput
      payload := .ke_plain (.key shared_key)
    }
    label_matches := rfl
  }

def responder_key_envelope
    (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := ke_receiver_to_smc_receiver_port
    message := {
      source := some ke_receiver_id
      label := .subroutineOutput
      payload := .ke_plain (.key shared_key)
    }
    label_matches := rfl
  }

def initiator_receive (st : InitiatorState)
    (msg : Message SMCEasyUCPayload) :
    InitiatorState :=
  match st.phase, msg.label, msg.payload with
  | .waiting_init, .input, .ke_plain .init =>
      { st with
        phase := .waiting_second
        pending_action := some .send_first }
  | .waiting_second, .subroutineOutput,
      .forw_from_functionality _ (.delivered _ _ (.ke_second share)) =>
      { st with pending_action := some (.output_key share) }
  | _, _, _ =>
      st

def responder_receive (st : ResponderState)
    (msg : Message SMCEasyUCPayload) :
    ResponderState :=
  match st.phase, msg.label, msg.payload with
  | .waiting_first, .subroutineOutput,
      .forw_from_functionality _ (.delivered _ _ (.ke_first share)) =>
      { st with pending_peer_share := some share }
  | _, _, _ =>
      st

noncomputable def initiator_resume
    (gen : GroupGenerator)
    (st : InitiatorState) :
    PMF (ActivationResult SMCEasyUCPayload InitiatorState) :=
  match st.pending_action with
  | none =>
      PMF.pure {
        state := st
        outgoing? := none
      }
  | some .send_first =>
      (match st.secret? with
        | some secret => PMF.pure secret
        | none =>
            match st.group? with
            | some G => sample_dh_secret_in_group G
            | none => sample_dh_secret gen st.sec_param).bind fun secret =>
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
              source := some ke_sender_id
              label := .input
              payload := .forw_plain
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
    (gen : GroupGenerator)
    (st : ResponderState) :
    PMF (ActivationResult SMCEasyUCPayload ResponderState) :=
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
            | none =>
                match st.group? with
                | some G => sample_dh_secret_in_group G
                | none => sample_dh_secret gen st.sec_param).bind fun secret =>
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
                  source := some ke_receiver_id
                  label := .input
                  payload := .forw_plain
                    (.submit ke_receiver_id ke_sender_id
                      (.ke_second secret.public_share))
                }
                label_matches := rfl
              }
            }

noncomputable def initiator_program
    (gen : GroupGenerator) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := InitiatorState
  init := initiator_init
  receive := initiator_receive
  resume := initiator_resume gen
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def responder_program
    (gen : GroupGenerator) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := ResponderState
  init := responder_init
  receive := responder_receive
  resume := responder_resume gen
  is_halted := fun _ => false
  output := fun _ => ()

/--
DHKE 这一步的理想 KE 功能机。

Dummy party ids 仍然是两个 KE party；external identities 是它们在外层 SMC
协议中的 caller，也就是 `smc_sender_id` 与 `smc_receiver_id`。
-/
noncomputable def ideal_ke_ids (gen : GroupGenerator) : KEIds where
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
  sample_key_material := sample_ideal_ke_key gen

/-- DHKE 子证明的目标理想功能。 -/
noncomputable def ideal_ke_functionality
    (gen : GroupGenerator) :
    IdealFunctionality SMCEasyUCPayload :=
  IdealKE (ideal_ke_ids gen)

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

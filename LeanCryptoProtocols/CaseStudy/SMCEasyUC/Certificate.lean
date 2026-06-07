import LeanCryptoProtocols.Assumptions.DDH
import LeanCryptoProtocols.UC.Functionality.Forw
import LeanCryptoProtocols.UC.Functionality.KE
import LeanCryptoProtocols.UC.Functionality.SMC
import LeanCryptoProtocols.UC.Security

/-!
# SMC EasyUC case study 的审计证书

本文件是当前 case study 的审计入口。它直接暴露：

- real SMC protocol 的机器组成；
- SMC 理想功能；
- 需要最终证明的 UC-realize 目标陈述。

这里不把 UC 安全证明本身伪装成已完成 theorem；本文件只给出精确的
certificate / theorem statement。
-/

set_option linter.flexible false
set_option linter.style.nativeDecide false

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Assumptions

/-! ## Certificate identities -/

def cert_smc_sender_id : MachineId := 10
def cert_smc_receiver_id : MachineId := 11
def cert_ke_sender_id : MachineId := 12
def cert_ke_receiver_id : MachineId := 13
def cert_forw_ke_forward_id : MachineId := 14
def cert_forw_ke_return_id : MachineId := 15
def cert_forw_smc_id : MachineId := 16
def cert_ideal_smc_id : MachineId := 17
def cert_sender_external_id : MachineId := 18
def cert_receiver_external_id : MachineId := 19

/-- 审计入口中固定的 real-world machine identities。 -/
def certificate_machine_id_list : List MachineId :=
  [ cert_smc_sender_id
  , cert_smc_receiver_id
  , cert_ke_sender_id
  , cert_ke_receiver_id
  , cert_forw_ke_forward_id
  , cert_forw_ke_return_id
  , cert_forw_smc_id
  ]

/-- 敌手在该 case study 中只能看到这三个 forwarding functionalities。 -/
def certificate_visible_to_adversary : Finset MachineId :=
  {cert_forw_ke_forward_id, cert_forw_ke_return_id, cert_forw_smc_id}

private theorem cert_id_ne_of_decide {a b : MachineId} (h : decide (a ≠ b) = true) :
    a ≠ b := by
  exact of_decide_eq_true h

private theorem cert_smc_sender_ne_smc_receiver :
    cert_smc_sender_id ≠ cert_smc_receiver_id := by decide

private theorem cert_smc_sender_ne_ke_sender :
    cert_smc_sender_id ≠ cert_ke_sender_id := by decide

private theorem cert_smc_sender_ne_ke_receiver :
    cert_smc_sender_id ≠ cert_ke_receiver_id := by decide

private theorem cert_smc_sender_ne_forw_ke_forward :
    cert_smc_sender_id ≠ cert_forw_ke_forward_id := by decide

private theorem cert_smc_sender_ne_forw_ke_return :
    cert_smc_sender_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_smc_sender_ne_forw_smc :
    cert_smc_sender_id ≠ cert_forw_smc_id := by decide

private theorem cert_smc_sender_ne_ideal_smc :
    cert_smc_sender_id ≠ cert_ideal_smc_id := by decide

private theorem cert_smc_receiver_ne_ke_sender :
    cert_smc_receiver_id ≠ cert_ke_sender_id := by decide

private theorem cert_smc_receiver_ne_ke_receiver :
    cert_smc_receiver_id ≠ cert_ke_receiver_id := by decide

private theorem cert_smc_receiver_ne_forw_ke_forward :
    cert_smc_receiver_id ≠ cert_forw_ke_forward_id := by decide

private theorem cert_smc_receiver_ne_forw_ke_return :
    cert_smc_receiver_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_smc_receiver_ne_forw_smc :
    cert_smc_receiver_id ≠ cert_forw_smc_id := by decide

private theorem cert_smc_receiver_ne_ideal_smc :
    cert_smc_receiver_id ≠ cert_ideal_smc_id := by decide

private theorem cert_ke_sender_ne_ke_receiver :
    cert_ke_sender_id ≠ cert_ke_receiver_id := by decide

private theorem cert_ke_sender_ne_forw_ke_forward :
    cert_ke_sender_id ≠ cert_forw_ke_forward_id := by decide

private theorem cert_ke_sender_ne_forw_ke_return :
    cert_ke_sender_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_ke_sender_ne_forw_smc :
    cert_ke_sender_id ≠ cert_forw_smc_id := by decide

private theorem cert_ke_receiver_ne_forw_ke_forward :
    cert_ke_receiver_id ≠ cert_forw_ke_forward_id := by decide

private theorem cert_ke_receiver_ne_forw_ke_return :
    cert_ke_receiver_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_ke_receiver_ne_forw_smc :
    cert_ke_receiver_id ≠ cert_forw_smc_id := by decide

private theorem cert_forw_ke_forward_ne_forw_ke_return :
    cert_forw_ke_forward_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_forw_ke_forward_ne_forw_smc :
    cert_forw_ke_forward_id ≠ cert_forw_smc_id := by decide

private theorem cert_forw_ke_return_ne_forw_smc :
    cert_forw_ke_return_id ≠ cert_forw_smc_id := by decide

private theorem cert_sender_external_ne_smc_sender :
    cert_sender_external_id ≠ cert_smc_sender_id := by decide

private theorem cert_sender_external_ne_smc_receiver :
    cert_sender_external_id ≠ cert_smc_receiver_id := by decide

private theorem cert_sender_external_ne_ke_sender :
    cert_sender_external_id ≠ cert_ke_sender_id := by decide

private theorem cert_sender_external_ne_ke_receiver :
    cert_sender_external_id ≠ cert_ke_receiver_id := by decide

private theorem cert_sender_external_ne_forw_ke_forward :
    cert_sender_external_id ≠ cert_forw_ke_forward_id := by decide

private theorem cert_sender_external_ne_forw_ke_return :
    cert_sender_external_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_sender_external_ne_forw_smc :
    cert_sender_external_id ≠ cert_forw_smc_id := by decide

private theorem cert_sender_external_ne_ideal_smc :
    cert_sender_external_id ≠ cert_ideal_smc_id := by decide

private theorem cert_receiver_external_ne_smc_sender :
    cert_receiver_external_id ≠ cert_smc_sender_id := by decide

private theorem cert_receiver_external_ne_smc_receiver :
    cert_receiver_external_id ≠ cert_smc_receiver_id := by decide

private theorem cert_receiver_external_ne_ke_sender :
    cert_receiver_external_id ≠ cert_ke_sender_id := by decide

private theorem cert_receiver_external_ne_ke_receiver :
    cert_receiver_external_id ≠ cert_ke_receiver_id := by decide

private theorem cert_receiver_external_ne_forw_ke_forward :
    cert_receiver_external_id ≠ cert_forw_ke_forward_id := by decide

private theorem cert_receiver_external_ne_forw_ke_return :
    cert_receiver_external_id ≠ cert_forw_ke_return_id := by decide

private theorem cert_receiver_external_ne_forw_smc :
    cert_receiver_external_id ≠ cert_forw_smc_id := by decide

private theorem cert_receiver_external_ne_ideal_smc :
    cert_receiver_external_id ≠ cert_ideal_smc_id := by decide

private theorem cert_sender_external_ne_receiver_external :
    cert_sender_external_id ≠ cert_receiver_external_id := by decide

private theorem cert_smc_sender_separated :
    cert_smc_sender_id ≠ env_id ∧ cert_smc_sender_id ≠ adv_id := by decide

private theorem cert_smc_receiver_separated :
    cert_smc_receiver_id ≠ env_id ∧ cert_smc_receiver_id ≠ adv_id := by decide

private theorem cert_ke_sender_separated :
    cert_ke_sender_id ≠ env_id ∧ cert_ke_sender_id ≠ adv_id := by decide

private theorem cert_ke_receiver_separated :
    cert_ke_receiver_id ≠ env_id ∧ cert_ke_receiver_id ≠ adv_id := by decide

private theorem cert_forw_ke_forward_separated :
    cert_forw_ke_forward_id ≠ env_id ∧ cert_forw_ke_forward_id ≠ adv_id := by decide

private theorem cert_forw_ke_return_separated :
    cert_forw_ke_return_id ≠ env_id ∧ cert_forw_ke_return_id ≠ adv_id := by decide

private theorem cert_forw_smc_separated :
    cert_forw_smc_id ≠ env_id ∧ cert_forw_smc_id ≠ adv_id := by decide

private theorem cert_ideal_smc_separated :
    cert_ideal_smc_id ≠ env_id ∧ cert_ideal_smc_id ≠ adv_id := by decide

private theorem cert_sender_external_separated :
    cert_sender_external_id ≠ env_id ∧ cert_sender_external_id ≠ adv_id := by decide

private theorem cert_receiver_external_separated :
    cert_receiver_external_id ≠ env_id ∧ cert_receiver_external_id ≠ adv_id := by decide

/-! ## Functionality identities -/

def certificate_forw_ke_forward_ids : ForwIds where
  sender_id := cert_ke_sender_id
  receiver_id := cert_ke_receiver_id
  functionality_id := cert_forw_ke_forward_id
  sender_external_id := cert_smc_sender_id
  receiver_external_id := cert_smc_receiver_id
  sender_ne_receiver := cert_ke_sender_ne_ke_receiver
  sender_ne_functionality := cert_ke_sender_ne_forw_ke_forward
  receiver_ne_functionality := cert_ke_receiver_ne_forw_ke_forward
  sender_id_separated := cert_ke_sender_separated
  receiver_id_separated := cert_ke_receiver_separated
  functionality_separated := cert_forw_ke_forward_separated
  sender_external_separated :=
    ⟨cert_smc_sender_ne_ke_sender, cert_smc_sender_ne_ke_receiver,
      cert_smc_sender_ne_forw_ke_forward, cert_smc_sender_separated.1,
      cert_smc_sender_separated.2⟩
  receiver_external_separated :=
    ⟨cert_smc_receiver_ne_ke_sender, cert_smc_receiver_ne_ke_receiver,
      cert_smc_receiver_ne_forw_ke_forward, cert_smc_receiver_separated.1,
      cert_smc_receiver_separated.2⟩

def certificate_forw_ke_return_ids : ForwIds where
  sender_id := cert_ke_receiver_id
  receiver_id := cert_ke_sender_id
  functionality_id := cert_forw_ke_return_id
  sender_external_id := cert_smc_receiver_id
  receiver_external_id := cert_smc_sender_id
  sender_ne_receiver := cert_ke_sender_ne_ke_receiver.symm
  sender_ne_functionality := cert_ke_receiver_ne_forw_ke_return
  receiver_ne_functionality := cert_ke_sender_ne_forw_ke_return
  sender_id_separated := cert_ke_receiver_separated
  receiver_id_separated := cert_ke_sender_separated
  functionality_separated := cert_forw_ke_return_separated
  sender_external_separated :=
    ⟨cert_smc_receiver_ne_ke_receiver, cert_smc_receiver_ne_ke_sender,
      cert_smc_receiver_ne_forw_ke_return, cert_smc_receiver_separated.1,
      cert_smc_receiver_separated.2⟩
  receiver_external_separated :=
    ⟨cert_smc_sender_ne_ke_receiver, cert_smc_sender_ne_ke_sender,
      cert_smc_sender_ne_forw_ke_return, cert_smc_sender_separated.1,
      cert_smc_sender_separated.2⟩

def certificate_forw_smc_ids : ForwIds where
  sender_id := cert_smc_sender_id
  receiver_id := cert_smc_receiver_id
  functionality_id := cert_forw_smc_id
  sender_external_id := cert_sender_external_id
  receiver_external_id := cert_receiver_external_id
  sender_ne_receiver := cert_smc_sender_ne_smc_receiver
  sender_ne_functionality := cert_smc_sender_ne_forw_smc
  receiver_ne_functionality := cert_smc_receiver_ne_forw_smc
  sender_id_separated := cert_smc_sender_separated
  receiver_id_separated := cert_smc_receiver_separated
  functionality_separated := cert_forw_smc_separated
  sender_external_separated :=
    ⟨cert_sender_external_ne_smc_sender, cert_sender_external_ne_smc_receiver,
      cert_sender_external_ne_forw_smc, cert_sender_external_separated.1,
      cert_sender_external_separated.2⟩
  receiver_external_separated :=
    ⟨cert_receiver_external_ne_smc_sender, cert_receiver_external_ne_smc_receiver,
      cert_receiver_external_ne_forw_smc, cert_receiver_external_separated.1,
      cert_receiver_external_separated.2⟩

def certificate_smc_ids : SMCIds where
  sender_id := cert_smc_sender_id
  receiver_id := cert_smc_receiver_id
  functionality_id := cert_ideal_smc_id
  sender_external_id := cert_sender_external_id
  receiver_external_id := cert_receiver_external_id
  sender_ne_receiver := cert_smc_sender_ne_smc_receiver
  sender_ne_functionality := cert_smc_sender_ne_ideal_smc
  receiver_ne_functionality := cert_smc_receiver_ne_ideal_smc
  sender_id_separated := cert_smc_sender_separated
  receiver_id_separated := cert_smc_receiver_separated
  functionality_separated := cert_ideal_smc_separated
  sender_external_separated :=
    ⟨cert_sender_external_ne_smc_sender, cert_sender_external_ne_smc_receiver,
      cert_sender_external_ne_ideal_smc, cert_sender_external_separated.1,
      cert_sender_external_separated.2⟩
  receiver_external_separated :=
    ⟨cert_receiver_external_ne_smc_sender, cert_receiver_external_ne_smc_receiver,
      cert_receiver_external_ne_ideal_smc, cert_receiver_external_separated.1,
      cert_receiver_external_separated.2⟩

/-! ## Ports used by the real protocol -/

def cert_smc_sender_to_ke_sender_port : CommPort :=
  mk_input_port cert_smc_sender_id cert_ke_sender_id
    cert_smc_sender_ne_ke_sender
    cert_smc_sender_separated.2
    cert_ke_sender_separated.2

def cert_smc_sender_to_forw_smc_port : CommPort :=
  mk_input_port cert_smc_sender_id cert_forw_smc_id
    cert_smc_sender_ne_forw_smc
    cert_smc_sender_separated.2
    cert_forw_smc_separated.2

def cert_smc_sender_to_external_port : CommPort :=
  mk_subroutine_output_port cert_smc_sender_id cert_sender_external_id
    cert_sender_external_ne_smc_sender.symm
    cert_smc_sender_separated.2
    cert_sender_external_separated.2

def cert_smc_receiver_to_ke_receiver_port : CommPort :=
  mk_input_port cert_smc_receiver_id cert_ke_receiver_id
    cert_smc_receiver_ne_ke_receiver
    cert_smc_receiver_separated.2
    cert_ke_receiver_separated.2

def cert_smc_receiver_to_forw_smc_port : CommPort :=
  mk_input_port cert_smc_receiver_id cert_forw_smc_id
    cert_smc_receiver_ne_forw_smc
    cert_smc_receiver_separated.2
    cert_forw_smc_separated.2

def cert_smc_receiver_to_external_port : CommPort :=
  mk_subroutine_output_port cert_smc_receiver_id cert_receiver_external_id
    cert_receiver_external_ne_smc_receiver.symm
    cert_smc_receiver_separated.2
    cert_receiver_external_separated.2

def cert_ke_sender_to_smc_sender_port : CommPort :=
  mk_subroutine_output_port cert_ke_sender_id cert_smc_sender_id
    cert_smc_sender_ne_ke_sender.symm
    cert_ke_sender_separated.2
    cert_smc_sender_separated.2

def cert_ke_sender_to_forw_ke_forward_port : CommPort :=
  mk_input_port cert_ke_sender_id cert_forw_ke_forward_id
    cert_ke_sender_ne_forw_ke_forward
    cert_ke_sender_separated.2
    cert_forw_ke_forward_separated.2

def cert_ke_sender_to_forw_ke_return_port : CommPort :=
  mk_input_port cert_ke_sender_id cert_forw_ke_return_id
    cert_ke_sender_ne_forw_ke_return
    cert_ke_sender_separated.2
    cert_forw_ke_return_separated.2

def cert_ke_receiver_to_smc_receiver_port : CommPort :=
  mk_subroutine_output_port cert_ke_receiver_id cert_smc_receiver_id
    cert_smc_receiver_ne_ke_receiver.symm
    cert_ke_receiver_separated.2
    cert_smc_receiver_separated.2

def cert_ke_receiver_to_forw_ke_forward_port : CommPort :=
  mk_input_port cert_ke_receiver_id cert_forw_ke_forward_id
    cert_ke_receiver_ne_forw_ke_forward
    cert_ke_receiver_separated.2
    cert_forw_ke_forward_separated.2

def cert_ke_receiver_to_forw_ke_return_port : CommPort :=
  mk_input_port cert_ke_receiver_id cert_forw_ke_return_id
    cert_ke_receiver_ne_forw_ke_return
    cert_ke_receiver_separated.2
    cert_forw_ke_return_separated.2

/-! ## Pseudocode-faithful local programs -/

private noncomputable def cert_option_resume {State : Type}
    (get : State → Option (Envelope SMCEasyUCPayload))
    (clear : State → State)
    (st : State) : PMF (ActivationResult SMCEasyUCPayload State) :=
  match get st with
  | none => PMF.pure { state := st, outgoing? := none }
  | some env => PMF.pure { state := clear st, outgoing? := some env }

def cert_lookup_key : List (Sid × SharedKey) → Sid → SharedKey
  | [], _ => default_shared_key
  | (sid', key) :: rest, sid =>
      if sid' = sid then key else cert_lookup_key rest sid

def cert_insert_key_if_absent
    (keys : List (Sid × SharedKey)) (sid : Sid) (key : SharedKey) :
    List (Sid × SharedKey) :=
  match keys with
  | [] => [(sid, key)]
  | (sid', key') :: rest =>
      if sid' = sid then
        (sid', key') :: rest
      else
        (sid', key') :: cert_insert_key_if_absent rest sid key

noncomputable def cert_sample_public_group_element
    (gen : PPTGroupGenerator) (n : ℕ) : PMF GroupElement :=
  (gen.run n).bind fun G =>
    G.sample_exponent.bind fun a =>
      PMF.pure ⟨G.encode (G.pow G.generator a)⟩

structure CertSMCSenderState where
  waiting_message : Option (Sid × Plaintext)
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

structure CertSMCReceiverState where
  session_keys : List (Sid × SharedKey)
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

inductive CertKESenderAction where
  | send_first (sid : Sid) (ssid : Ssid)
  | output_key (sid : Sid) (ssid : Ssid) (peer_share : GroupElement)

structure CertKESenderState where
  sec_param : ℕ
  local_share : Option GroupElement
  pending_action : Option CertKESenderAction

structure CertKEReceiverState where
  sec_param : ℕ
  pending_action : Option (Sid × Ssid × GroupElement)
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

def cert_ke_sender_init (n : ℕ) : CertKESenderState := {
  sec_param := n
  local_share := none
  pending_action := none
}

def cert_ke_receiver_init (n : ℕ) : CertKEReceiverState := {
  sec_param := n
  pending_action := none
  pending_outgoing := none
}

def cert_smc_sender_receive (st : CertSMCSenderState)
    (msg : Message SMCEasyUCPayload) : CertSMCSenderState :=
  match msg.payload with
  | .smc_plain (.send sid plaintext) =>
      { waiting_message := some (sid, plaintext)
        pending_outgoing := some {
          port := cert_smc_sender_to_ke_sender_port
          message := {
            source := some cert_smc_sender_id
            label := .input
            payload := .ke_plain (.init sid 0)
          }
          label_matches := rfl
        } }
  | .ke_plain (.key sid _ shared_key) =>
      match st.waiting_message with
      | some (sid', plaintext) =>
          if sid = sid' then
            { waiting_message := none
              pending_outgoing := some {
                port := cert_smc_sender_to_forw_smc_port
                message := {
                  source := some cert_smc_sender_id
                  label := .input
                  payload := .forw_plain
                    (.submit sid cert_smc_sender_id cert_smc_receiver_id
                      (.smc_cipher sid (enc shared_key plaintext)))
                }
                label_matches := rfl
              } }
          else
            st
      | none => st
  | _ => st

def cert_smc_receiver_receive (st : CertSMCReceiverState)
    (msg : Message SMCEasyUCPayload) : CertSMCReceiverState :=
  match msg.payload with
  | .ke_plain (.key sid _ shared_key) =>
      { session_keys := cert_insert_key_if_absent st.session_keys sid shared_key
        pending_outgoing := none }
  | .forw_from_functionality _ (.delivered sid _ _ (.smc_cipher _ cipher)) =>
      let shared_key := cert_lookup_key st.session_keys sid
      { st with
        pending_outgoing := some {
          port := cert_smc_receiver_to_external_port
          message := {
            source := some cert_smc_receiver_id
            label := .subroutineOutput
            payload := .smc_plain (.received sid (dec shared_key cipher))
          }
          label_matches := rfl
        } }
  | _ => st

def cert_ke_sender_receive (st : CertKESenderState)
    (msg : Message SMCEasyUCPayload) : CertKESenderState :=
  match msg.payload with
  | .ke_plain (.init sid ssid) =>
      { st with pending_action := some (.send_first sid ssid) }
  | .forw_from_functionality _ (.delivered sid _ _ (.ke_second _ ssid share)) =>
      { st with pending_action := some (.output_key sid ssid share) }
  | _ => st

def cert_ke_receiver_receive (st : CertKEReceiverState)
    (msg : Message SMCEasyUCPayload) : CertKEReceiverState :=
  match msg.payload with
  | .forw_from_functionality _ (.delivered sid _ _ (.ke_first _ ssid share)) =>
      { st with pending_action := some (sid, ssid, share) }
  | _ => st

private def cert_ke_sender_key_envelope
    (sid : Sid) (ssid : Ssid) (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := cert_ke_sender_to_smc_sender_port
    message := {
      source := some cert_ke_sender_id
      label := .subroutineOutput
      payload := .ke_plain (.key sid ssid shared_key)
    }
    label_matches := rfl
  }

private def cert_ke_receiver_key_envelope
    (sid : Sid) (ssid : Ssid) (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := cert_ke_receiver_to_smc_receiver_port
    message := {
      source := some cert_ke_receiver_id
      label := .subroutineOutput
      payload := .ke_plain (.key sid ssid shared_key)
    }
    label_matches := rfl
  }

noncomputable def cert_ke_sender_resume
    (gen : PPTGroupGenerator)
    (st : CertKESenderState) : PMF (ActivationResult SMCEasyUCPayload CertKESenderState) :=
  match st.pending_action with
  | none => PMF.pure { state := st, outgoing? := none }
  | some (.send_first sid ssid) =>
      cert_sample_public_group_element gen st.sec_param |>.bind fun share =>
        PMF.pure {
          state := { st with local_share := some share, pending_action := none }
          outgoing? := some {
            port := cert_ke_sender_to_forw_ke_forward_port
            message := {
              source := some cert_ke_sender_id
              label := .input
              payload := .forw_plain
                (.submit sid cert_ke_sender_id cert_ke_receiver_id (.ke_first sid ssid share))
            }
            label_matches := rfl
          }
        }
  | some (.output_key sid ssid peer_share) =>
      let shared_key :=
        match st.local_share with
        | some share => derive_shared_key share peer_share
        | none => default_shared_key
      PMF.pure {
        state := { st with local_share := none, pending_action := none }
        outgoing? := some (cert_ke_sender_key_envelope sid ssid shared_key)
      }

noncomputable def cert_ke_receiver_resume
    (gen : PPTGroupGenerator)
    (st : CertKEReceiverState) :
    PMF (ActivationResult SMCEasyUCPayload CertKEReceiverState) :=
  match st.pending_outgoing with
  | some env =>
      PMF.pure { state := { st with pending_outgoing := none }, outgoing? := some env }
  | none =>
      match st.pending_action with
      | none => PMF.pure { state := st, outgoing? := none }
      | some (sid, ssid, peer_share) =>
          cert_sample_public_group_element gen st.sec_param |>.bind fun share =>
            let shared_key := derive_shared_key peer_share share
            PMF.pure {
              state := {
                st with
                  pending_action := none
                  pending_outgoing := some (cert_ke_receiver_key_envelope sid ssid shared_key)
              }
              outgoing? := some {
                port := cert_ke_receiver_to_forw_ke_return_port
                message := {
                  source := some cert_ke_receiver_id
                  label := .input
                  payload := .forw_plain
                    (.submit sid cert_ke_receiver_id cert_ke_sender_id
                      (.ke_second sid ssid share))
                }
                label_matches := rfl
              }
            }

noncomputable def certificate_smc_sender_program :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := CertSMCSenderState
  init := fun _ => { waiting_message := none, pending_outgoing := none }
  receive := cert_smc_sender_receive
  resume :=
    cert_option_resume
      (fun st => st.pending_outgoing)
      (fun st => { st with pending_outgoing := none })
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def certificate_smc_receiver_program :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := CertSMCReceiverState
  init := fun _ => { session_keys := [], pending_outgoing := none }
  receive := cert_smc_receiver_receive
  resume :=
    cert_option_resume
      (fun st => st.pending_outgoing)
      (fun st => { st with pending_outgoing := none })
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def certificate_ke_sender_program
    (gen : PPTGroupGenerator) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := CertKESenderState
  init := cert_ke_sender_init
  receive := cert_ke_sender_receive
  resume := cert_ke_sender_resume gen
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def certificate_ke_receiver_program
    (gen : PPTGroupGenerator) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := CertKEReceiverState
  init := cert_ke_receiver_init
  receive := cert_ke_receiver_receive
  resume := cert_ke_receiver_resume gen
  is_halted := fun _ => false
  output := fun _ => ()

/-! ## Machines -/

noncomputable def certificate_smc_sender_machine : Machine SMCEasyUCPayload Unit where
  id := cert_smc_sender_id
  communication_set :=
    { cert_smc_sender_to_ke_sender_port
    , cert_smc_sender_to_forw_smc_port
    , cert_smc_sender_to_external_port
    }
  program := certificate_smc_sender_program
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [cert_smc_sender_to_ke_sender_port, cert_smc_sender_to_forw_smc_port,
        cert_smc_sender_to_external_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [cert_smc_sender_to_ke_sender_port, cert_smc_sender_to_forw_smc_port,
        cert_smc_sender_to_external_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (cert_ke_sender_ne_forw_smc
          (by
            simpa [cert_smc_sender_to_ke_sender_port,
              cert_smc_sender_to_forw_smc_port] using h_dest)).elim
      · exact (cert_sender_external_ne_ke_sender
          (by
            simpa [cert_smc_sender_to_ke_sender_port,
              cert_smc_sender_to_external_port] using h_dest.symm)).elim
      · exact (cert_ke_sender_ne_forw_smc
          (by
            simpa [cert_smc_sender_to_ke_sender_port,
              cert_smc_sender_to_forw_smc_port] using h_dest.symm)).elim
      · rfl
      · exact (cert_sender_external_ne_forw_smc
          (by
            simpa [cert_smc_sender_to_forw_smc_port,
              cert_smc_sender_to_external_port] using h_dest.symm)).elim
      · exact (cert_sender_external_ne_ke_sender
          (by
            simpa [cert_smc_sender_to_ke_sender_port,
              cert_smc_sender_to_external_port] using h_dest)).elim
      · exact (cert_sender_external_ne_forw_smc
          (by
            simpa [cert_smc_sender_to_forw_smc_port,
              cert_smc_sender_to_external_port] using h_dest)).elim
      · rfl

noncomputable def certificate_smc_receiver_machine : Machine SMCEasyUCPayload Unit where
  id := cert_smc_receiver_id
  communication_set :=
    { cert_smc_receiver_to_ke_receiver_port
    , cert_smc_receiver_to_forw_smc_port
    , cert_smc_receiver_to_external_port
    }
  program := certificate_smc_receiver_program
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [cert_smc_receiver_to_ke_receiver_port, cert_smc_receiver_to_forw_smc_port,
        cert_smc_receiver_to_external_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [cert_smc_receiver_to_ke_receiver_port, cert_smc_receiver_to_forw_smc_port,
        cert_smc_receiver_to_external_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (cert_ke_receiver_ne_forw_smc
          (by
            simpa [cert_smc_receiver_to_ke_receiver_port,
              cert_smc_receiver_to_forw_smc_port] using h_dest)).elim
      · exact (cert_receiver_external_ne_ke_receiver
          (by
            simpa [cert_smc_receiver_to_ke_receiver_port,
              cert_smc_receiver_to_external_port] using h_dest.symm)).elim
      · exact (cert_ke_receiver_ne_forw_smc
          (by
            simpa [cert_smc_receiver_to_ke_receiver_port,
              cert_smc_receiver_to_forw_smc_port] using h_dest.symm)).elim
      · rfl
      · exact (cert_receiver_external_ne_forw_smc
          (by
            simpa [cert_smc_receiver_to_forw_smc_port,
              cert_smc_receiver_to_external_port] using h_dest.symm)).elim
      · exact (cert_receiver_external_ne_ke_receiver
          (by
            simpa [cert_smc_receiver_to_ke_receiver_port,
              cert_smc_receiver_to_external_port] using h_dest)).elim
      · exact (cert_receiver_external_ne_forw_smc
          (by
            simpa [cert_smc_receiver_to_forw_smc_port,
              cert_smc_receiver_to_external_port] using h_dest)).elim
      · rfl

noncomputable def certificate_ke_sender_machine
    (gen : PPTGroupGenerator) : Machine SMCEasyUCPayload Unit where
  id := cert_ke_sender_id
  communication_set :=
    { cert_ke_sender_to_smc_sender_port
    , cert_ke_sender_to_forw_ke_forward_port
    , cert_ke_sender_to_forw_ke_return_port
    }
  program := certificate_ke_sender_program gen
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [cert_ke_sender_to_smc_sender_port, cert_ke_sender_to_forw_ke_forward_port,
        cert_ke_sender_to_forw_ke_return_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [cert_ke_sender_to_smc_sender_port, cert_ke_sender_to_forw_ke_forward_port,
        cert_ke_sender_to_forw_ke_return_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (cert_smc_sender_ne_forw_ke_forward
          (by
            simpa [cert_ke_sender_to_smc_sender_port,
              cert_ke_sender_to_forw_ke_forward_port] using h_dest)).elim
      · exact (cert_smc_sender_ne_forw_ke_return
          (by
            simpa [cert_ke_sender_to_smc_sender_port,
              cert_ke_sender_to_forw_ke_return_port] using h_dest)).elim
      · exact (cert_smc_sender_ne_forw_ke_forward
          (by
            simpa [cert_ke_sender_to_smc_sender_port,
              cert_ke_sender_to_forw_ke_forward_port] using h_dest.symm)).elim
      · rfl
      · exact (cert_forw_ke_forward_ne_forw_ke_return
          (by
            simpa [cert_ke_sender_to_forw_ke_forward_port,
              cert_ke_sender_to_forw_ke_return_port] using h_dest)).elim
      · exact (cert_smc_sender_ne_forw_ke_return
          (by
            simpa [cert_ke_sender_to_smc_sender_port,
              cert_ke_sender_to_forw_ke_return_port] using h_dest.symm)).elim
      · exact (cert_forw_ke_forward_ne_forw_ke_return
          (by
            simpa [cert_ke_sender_to_forw_ke_forward_port,
              cert_ke_sender_to_forw_ke_return_port] using h_dest.symm)).elim
      · rfl

noncomputable def certificate_ke_receiver_machine
    (gen : PPTGroupGenerator) : Machine SMCEasyUCPayload Unit where
  id := cert_ke_receiver_id
  communication_set :=
    { cert_ke_receiver_to_smc_receiver_port
    , cert_ke_receiver_to_forw_ke_forward_port
    , cert_ke_receiver_to_forw_ke_return_port
    }
  program := certificate_ke_receiver_program gen
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [cert_ke_receiver_to_smc_receiver_port, cert_ke_receiver_to_forw_ke_forward_port,
        cert_ke_receiver_to_forw_ke_return_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [cert_ke_receiver_to_smc_receiver_port, cert_ke_receiver_to_forw_ke_forward_port,
        cert_ke_receiver_to_forw_ke_return_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (cert_smc_receiver_ne_forw_ke_forward
          (by
            simpa [cert_ke_receiver_to_smc_receiver_port,
              cert_ke_receiver_to_forw_ke_forward_port] using h_dest)).elim
      · exact (cert_smc_receiver_ne_forw_ke_return
          (by
            simpa [cert_ke_receiver_to_smc_receiver_port,
              cert_ke_receiver_to_forw_ke_return_port] using h_dest)).elim
      · exact (cert_smc_receiver_ne_forw_ke_forward
          (by
            simpa [cert_ke_receiver_to_smc_receiver_port,
              cert_ke_receiver_to_forw_ke_forward_port] using h_dest.symm)).elim
      · rfl
      · exact (cert_forw_ke_forward_ne_forw_ke_return
          (by
            simpa [cert_ke_receiver_to_forw_ke_forward_port,
              cert_ke_receiver_to_forw_ke_return_port] using h_dest)).elim
      · exact (cert_smc_receiver_ne_forw_ke_return
          (by
            simpa [cert_ke_receiver_to_smc_receiver_port,
              cert_ke_receiver_to_forw_ke_return_port] using h_dest.symm)).elim
      · exact (cert_forw_ke_forward_ne_forw_ke_return
          (by
            simpa [cert_ke_receiver_to_forw_ke_forward_port,
              cert_ke_receiver_to_forw_ke_return_port] using h_dest.symm)).elim
      · rfl

private theorem cert_forw_has_subroutine_to_sender
    (ids : ForwIds) :
    is_subroutine_of_id (IdealForw ids).machine ids.sender_id := by
  refine ⟨forw_sender_port ids, ?_, rfl, rfl⟩
  change forw_sender_port ids ∈ Functionality.ForwImpl.communication_set ids
  simp [Functionality.ForwImpl.communication_set]

private theorem cert_forw_has_subroutine_to_receiver
    (ids : ForwIds) :
    is_subroutine_of_id (IdealForw ids).machine ids.receiver_id := by
  refine ⟨forw_receiver_port ids, ?_, rfl, rfl⟩
  change forw_receiver_port ids ∈ Functionality.ForwImpl.communication_set ids
  simp [Functionality.ForwImpl.communication_set]

private theorem cert_ke_sender_is_subroutine_of_smc_sender
    (gen : PPTGroupGenerator) :
    is_subroutine_of_id (certificate_ke_sender_machine gen) cert_smc_sender_id := by
  refine ⟨cert_ke_sender_to_smc_sender_port, ?_, rfl, rfl⟩
  simp [certificate_ke_sender_machine]

private theorem cert_ke_receiver_is_subroutine_of_smc_receiver
    (gen : PPTGroupGenerator) :
    is_subroutine_of_id (certificate_ke_receiver_machine gen) cert_smc_receiver_id := by
  refine ⟨cert_ke_receiver_to_smc_receiver_port, ?_, rfl, rfl⟩
  simp [certificate_ke_receiver_machine]

/-! ## Protocol -/

noncomputable def certificate_real_smc_machines
    (gen : PPTGroupGenerator) : List (AnyMachine SMCEasyUCPayload) :=
  [ ⟨Unit, certificate_smc_sender_machine⟩
  , ⟨Unit, certificate_smc_receiver_machine⟩
  , ⟨Unit, certificate_ke_sender_machine gen⟩
  , ⟨Unit, certificate_ke_receiver_machine gen⟩
  , ⟨Unit, (IdealForw certificate_forw_ke_forward_ids).machine⟩
  , ⟨Unit, (IdealForw certificate_forw_ke_return_ids).machine⟩
  , ⟨Unit, (IdealForw certificate_forw_smc_ids).machine⟩
  ]

theorem certificate_real_smc_unique_ids
    (gen : PPTGroupGenerator) :
    (machine_ids (certificate_real_smc_machines gen)).Nodup := by
  change
    [ cert_smc_sender_id
    , cert_smc_receiver_id
    , cert_ke_sender_id
    , cert_ke_receiver_id
    , cert_forw_ke_forward_id
    , cert_forw_ke_return_id
    , cert_forw_smc_id
    ].Nodup
  native_decide

theorem certificate_real_smc_caller_has_matching_subroutine
    (gen : PPTGroupGenerator) :
  ∀ m ∈ certificate_real_smc_machines gen, ∀ mid : MachineId,
    is_caller_of_id m.2 mid →
      ∃ m' ∈ certificate_real_smc_machines gen,
        AnyMachine.id m' = mid ∧ is_subroutine_of_id m'.2 (AnyMachine.id m) := by
  intro m hm mid h_caller
  simp [certificate_real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_smc_sender_machine, cert_smc_sender_to_ke_sender_port,
      cert_smc_sender_to_forw_smc_port, cert_smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_ke_sender_id := by
        simpa [cert_smc_sender_to_ke_sender_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · simpa [AnyMachine.id] using cert_ke_sender_is_subroutine_of_smc_sender gen
    · have h_mid : mid = cert_forw_smc_id := by
        simpa [cert_smc_sender_to_forw_smc_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw certificate_forw_smc_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id, certificate_forw_smc_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, certificate_forw_smc_ids] using
          cert_forw_has_subroutine_to_sender certificate_forw_smc_ids
    · cases h_label
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_smc_receiver_machine, cert_smc_receiver_to_ke_receiver_port,
      cert_smc_receiver_to_forw_smc_port, cert_smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_ke_receiver_id := by
        simpa [cert_smc_receiver_to_ke_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · simpa [AnyMachine.id] using cert_ke_receiver_is_subroutine_of_smc_receiver gen
    · have h_mid : mid = cert_forw_smc_id := by
        simpa [cert_smc_receiver_to_forw_smc_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw certificate_forw_smc_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id, certificate_forw_smc_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, certificate_forw_smc_ids] using
          cert_forw_has_subroutine_to_receiver certificate_forw_smc_ids
    · cases h_label
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_ke_sender_machine, cert_ke_sender_to_smc_sender_port,
      cert_ke_sender_to_forw_ke_forward_port, cert_ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = cert_forw_ke_forward_id := by
        simpa [cert_ke_sender_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw certificate_forw_ke_forward_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id, certificate_forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, certificate_forw_ke_forward_ids] using
          cert_forw_has_subroutine_to_sender certificate_forw_ke_forward_ids
    · have h_mid : mid = cert_forw_ke_return_id := by
        simpa [cert_ke_sender_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw certificate_forw_ke_return_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id, certificate_forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, certificate_forw_ke_return_ids] using
          cert_forw_has_subroutine_to_receiver certificate_forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_ke_receiver_machine, cert_ke_receiver_to_smc_receiver_port,
      cert_ke_receiver_to_forw_ke_forward_port, cert_ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = cert_forw_ke_forward_id := by
        simpa [cert_ke_receiver_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw certificate_forw_ke_forward_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id, certificate_forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, certificate_forw_ke_forward_ids] using
          cert_forw_has_subroutine_to_receiver certificate_forw_ke_forward_ids
    · have h_mid : mid = cert_forw_ke_return_id := by
        simpa [cert_ke_receiver_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw certificate_forw_ke_return_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id, certificate_forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, certificate_forw_ke_return_ids] using
          cert_forw_has_subroutine_to_sender certificate_forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set certificate_forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label

theorem certificate_real_smc_subroutine_has_matching_caller
    (gen : PPTGroupGenerator) :
  ∀ m ∈ certificate_real_smc_machines gen, ∀ mid : MachineId,
    is_subroutine_of_id m.2 mid →
      mid ∈ machine_ids (certificate_real_smc_machines gen) →
      ∃ m' ∈ certificate_real_smc_machines gen,
        AnyMachine.id m' = mid ∧ is_caller_of_id m'.2 (AnyMachine.id m) := by
  intro m hm mid h_sub h_mid_mem
  simp [certificate_real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_smc_sender_machine, cert_smc_sender_to_ke_sender_port,
      cert_smc_sender_to_forw_smc_port, cert_smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · cases h_label
    · have h_mid : mid = cert_sender_external_id := by
        simpa [cert_smc_sender_to_external_port] using h_dest.symm
      subst mid
      change cert_sender_external_id ∈ certificate_machine_id_list at h_mid_mem
      simp [certificate_machine_id_list] at h_mid_mem
      exfalso
      rcases h_mid_mem with h | h | h | h | h | h | h
      · exact cert_sender_external_ne_smc_sender h
      · exact cert_sender_external_ne_smc_receiver h
      · exact cert_sender_external_ne_ke_sender h
      · exact cert_sender_external_ne_ke_receiver h
      · exact cert_sender_external_ne_forw_ke_forward h
      · exact cert_sender_external_ne_forw_ke_return h
      · exact cert_sender_external_ne_forw_smc h
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_smc_receiver_machine, cert_smc_receiver_to_ke_receiver_port,
      cert_smc_receiver_to_forw_smc_port, cert_smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · cases h_label
    · have h_mid : mid = cert_receiver_external_id := by
        simpa [cert_smc_receiver_to_external_port] using h_dest.symm
      subst mid
      change cert_receiver_external_id ∈ certificate_machine_id_list at h_mid_mem
      simp [certificate_machine_id_list] at h_mid_mem
      exfalso
      rcases h_mid_mem with h | h | h | h | h | h | h
      · exact cert_receiver_external_ne_smc_sender h
      · exact cert_receiver_external_ne_smc_receiver h
      · exact cert_receiver_external_ne_ke_sender h
      · exact cert_receiver_external_ne_ke_receiver h
      · exact cert_receiver_external_ne_forw_ke_forward h
      · exact cert_receiver_external_ne_forw_ke_return h
      · exact cert_receiver_external_ne_forw_smc h
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_ke_sender_machine, cert_ke_sender_to_smc_sender_port,
      cert_ke_sender_to_forw_ke_forward_port, cert_ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_smc_sender_id := by
        simpa [cert_ke_sender_to_smc_sender_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_smc_sender_machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_smc_sender_to_ke_sender_port, ?_, rfl, rfl⟩
        simp [certificate_smc_sender_machine]
    · cases h_label
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [certificate_ke_receiver_machine, cert_ke_receiver_to_smc_receiver_port,
      cert_ke_receiver_to_forw_ke_forward_port, cert_ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_smc_receiver_id := by
        simpa [cert_ke_receiver_to_smc_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_smc_receiver_machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_smc_receiver_to_ke_receiver_port, ?_, rfl, rfl⟩
        simp [certificate_smc_receiver_machine]
    · cases h_label
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_ke_sender_id := by
        simpa [certificate_forw_ke_forward_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_ke_sender_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [certificate_ke_sender_machine]
    · have h_mid : mid = cert_ke_receiver_id := by
        simpa [certificate_forw_ke_forward_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_ke_receiver_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [certificate_ke_receiver_machine]
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_ke_receiver_id := by
        simpa [certificate_forw_ke_return_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_ke_receiver_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [certificate_ke_receiver_machine]
    · have h_mid : mid = cert_ke_sender_id := by
        simpa [certificate_forw_ke_return_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_ke_sender_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [certificate_ke_sender_machine]
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set certificate_forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = cert_smc_sender_id := by
        simpa [certificate_forw_smc_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_smc_sender_machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_smc_sender_to_forw_smc_port, ?_, rfl, rfl⟩
        simp [certificate_smc_sender_machine]
    · have h_mid : mid = cert_smc_receiver_id := by
        simpa [certificate_forw_smc_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, certificate_smc_receiver_machine⟩, ?_, ?_, ?_⟩
      · simp [certificate_real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨cert_smc_receiver_to_forw_smc_port, ?_, rfl, rfl⟩
        simp [certificate_smc_receiver_machine]
    · cases h_label

theorem certificate_real_smc_env_separated
    (gen : PPTGroupGenerator) :
    env_id ∉ machine_ids (certificate_real_smc_machines gen) := by
  change env_id ∉ certificate_machine_id_list
  native_decide

theorem certificate_real_smc_adv_separated
    (gen : PPTGroupGenerator) :
    adv_id ∉ machine_ids (certificate_real_smc_machines gen) := by
  change adv_id ∉ certificate_machine_id_list
  native_decide

theorem certificate_real_smc_no_direct_environment_communication
    (gen : PPTGroupGenerator) :
    ∀ m ∈ certificate_real_smc_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest ≠ env_id := by
  intro m hm p hp
  simp [certificate_real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [certificate_smc_sender_machine, cert_smc_sender_to_ke_sender_port,
      cert_smc_sender_to_forw_smc_port, cert_smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [certificate_smc_receiver_machine, cert_smc_receiver_to_ke_receiver_port,
      cert_smc_receiver_to_forw_smc_port, cert_smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [certificate_ke_sender_machine, cert_ke_sender_to_smc_sender_port,
      cert_ke_sender_to_forw_ke_forward_port, cert_ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [certificate_ke_receiver_machine, cert_ke_receiver_to_smc_receiver_port,
      cert_ke_receiver_to_forw_ke_forward_port, cert_ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide

theorem certificate_real_smc_adversary_communication_is_backdoor
    (gen : PPTGroupGenerator) :
    ∀ m ∈ certificate_real_smc_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest = adv_id → p.label = .backdoor := by
  intro m hm p hp h_dest
  simp [certificate_real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [certificate_smc_sender_machine, cert_smc_sender_to_ke_sender_port,
      cert_smc_sender_to_forw_smc_port, cert_smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_sender_id = adv_id := by
        simpa [cert_smc_sender_to_ke_sender_port, mk_input_port] using h_dest
      exact cert_ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_smc_id = adv_id := by
        simpa [cert_smc_sender_to_forw_smc_port, mk_input_port] using h_dest
      exact cert_forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : cert_sender_external_id = adv_id := by
        simpa [cert_smc_sender_to_external_port, mk_subroutine_output_port] using h_dest
      exact cert_sender_external_separated.2 h_bad
  · simp [certificate_smc_receiver_machine, cert_smc_receiver_to_ke_receiver_port,
      cert_smc_receiver_to_forw_smc_port, cert_smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_receiver_id = adv_id := by
        simpa [cert_smc_receiver_to_ke_receiver_port, mk_input_port] using h_dest
      exact cert_ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_smc_id = adv_id := by
        simpa [cert_smc_receiver_to_forw_smc_port, mk_input_port] using h_dest
      exact cert_forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : cert_receiver_external_id = adv_id := by
        simpa [cert_smc_receiver_to_external_port, mk_subroutine_output_port] using h_dest
      exact cert_receiver_external_separated.2 h_bad
  · simp [certificate_ke_sender_machine, cert_ke_sender_to_smc_sender_port,
      cert_ke_sender_to_forw_ke_forward_port, cert_ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_smc_sender_id = adv_id := by
        simpa [cert_ke_sender_to_smc_sender_port, mk_subroutine_output_port] using h_dest
      exact cert_smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_forward_id = adv_id := by
        simpa [cert_ke_sender_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact cert_forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_return_id = adv_id := by
        simpa [cert_ke_sender_to_forw_ke_return_port, mk_input_port] using h_dest
      exact cert_forw_ke_return_separated.2 h_bad
  · simp [certificate_ke_receiver_machine, cert_ke_receiver_to_smc_receiver_port,
      cert_ke_receiver_to_forw_ke_forward_port, cert_ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_smc_receiver_id = adv_id := by
        simpa [cert_ke_receiver_to_smc_receiver_port, mk_subroutine_output_port] using h_dest
      exact cert_smc_receiver_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_forward_id = adv_id := by
        simpa [cert_ke_receiver_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact cert_forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_return_id = adv_id := by
        simpa [cert_ke_receiver_to_forw_ke_return_port, mk_input_port] using h_dest
      exact cert_forw_ke_return_separated.2 h_bad
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_sender_id = adv_id := by
        simpa [forw_sender_port, certificate_forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_ke_receiver_id = adv_id := by
        simpa [forw_receiver_port, certificate_forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_receiver_separated.2 h_bad
    · rfl
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_receiver_id = adv_id := by
        simpa [forw_sender_port, certificate_forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : cert_ke_sender_id = adv_id := by
        simpa [forw_receiver_port, certificate_forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_sender_separated.2 h_bad
    · rfl
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_smc_sender_id = adv_id := by
        simpa [forw_sender_port, certificate_forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_smc_receiver_id = adv_id := by
        simpa [forw_receiver_port, certificate_forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_smc_receiver_separated.2 h_bad
    · rfl

/-- 审计约束：real-world adversary 的静态通信视野只包含三个 `Forw` functionality。 -/
theorem certificate_adversary_visible_only_forw
    (gen : PPTGroupGenerator) :
    ∀ m ∈ certificate_real_smc_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest = adv_id → AnyMachine.id m ∈ certificate_visible_to_adversary := by
  intro m hm p hp h_dest
  simp [certificate_real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [certificate_smc_sender_machine, cert_smc_sender_to_ke_sender_port,
      cert_smc_sender_to_forw_smc_port, cert_smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_sender_id = adv_id := by
        simpa [cert_smc_sender_to_ke_sender_port, mk_input_port] using h_dest
      exact cert_ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_smc_id = adv_id := by
        simpa [cert_smc_sender_to_forw_smc_port, mk_input_port] using h_dest
      exact cert_forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : cert_sender_external_id = adv_id := by
        simpa [cert_smc_sender_to_external_port, mk_subroutine_output_port] using h_dest
      exact cert_sender_external_separated.2 h_bad
  · simp [certificate_smc_receiver_machine, cert_smc_receiver_to_ke_receiver_port,
      cert_smc_receiver_to_forw_smc_port, cert_smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_receiver_id = adv_id := by
        simpa [cert_smc_receiver_to_ke_receiver_port, mk_input_port] using h_dest
      exact cert_ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_smc_id = adv_id := by
        simpa [cert_smc_receiver_to_forw_smc_port, mk_input_port] using h_dest
      exact cert_forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : cert_receiver_external_id = adv_id := by
        simpa [cert_smc_receiver_to_external_port, mk_subroutine_output_port] using h_dest
      exact cert_receiver_external_separated.2 h_bad
  · simp [certificate_ke_sender_machine, cert_ke_sender_to_smc_sender_port,
      cert_ke_sender_to_forw_ke_forward_port, cert_ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_smc_sender_id = adv_id := by
        simpa [cert_ke_sender_to_smc_sender_port, mk_subroutine_output_port] using h_dest
      exact cert_smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_forward_id = adv_id := by
        simpa [cert_ke_sender_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact cert_forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_return_id = adv_id := by
        simpa [cert_ke_sender_to_forw_ke_return_port, mk_input_port] using h_dest
      exact cert_forw_ke_return_separated.2 h_bad
  · simp [certificate_ke_receiver_machine, cert_ke_receiver_to_smc_receiver_port,
      cert_ke_receiver_to_forw_ke_forward_port, cert_ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_smc_receiver_id = adv_id := by
        simpa [cert_ke_receiver_to_smc_receiver_port, mk_subroutine_output_port] using h_dest
      exact cert_smc_receiver_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_forward_id = adv_id := by
        simpa [cert_ke_receiver_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact cert_forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : cert_forw_ke_return_id = adv_id := by
        simpa [cert_ke_receiver_to_forw_ke_return_port, mk_input_port] using h_dest
      exact cert_forw_ke_return_separated.2 h_bad
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_sender_id = adv_id := by
        simpa [forw_sender_port, certificate_forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_ke_receiver_id = adv_id := by
        simpa [forw_receiver_port, certificate_forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_receiver_separated.2 h_bad
    · change cert_forw_ke_forward_id ∈ certificate_visible_to_adversary
      simp [certificate_visible_to_adversary]
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_ke_receiver_id = adv_id := by
        simpa [forw_sender_port, certificate_forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : cert_ke_sender_id = adv_id := by
        simpa [forw_receiver_port, certificate_forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_ke_sender_separated.2 h_bad
    · change cert_forw_ke_return_id ∈ certificate_visible_to_adversary
      simp [certificate_visible_to_adversary]
  · change p ∈ Functionality.ForwImpl.communication_set certificate_forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : cert_smc_sender_id = adv_id := by
        simpa [forw_sender_port, certificate_forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : cert_smc_receiver_id = adv_id := by
        simpa [forw_receiver_port, certificate_forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact cert_smc_receiver_separated.2 h_bad
    · change cert_forw_smc_id ∈ certificate_visible_to_adversary
      simp [certificate_visible_to_adversary]

/-- 审计入口暴露的 real SMC protocol：2 个 main machines 与 5 个 internal machines。 -/
noncomputable def certificate_real_smc_protocol
    (gen : PPTGroupGenerator) : Protocol SMCEasyUCPayload :=
  { machines := certificate_real_smc_machines gen
    unique_ids := certificate_real_smc_unique_ids gen
    caller_has_matching_subroutine :=
      certificate_real_smc_caller_has_matching_subroutine gen
    subroutine_has_matching_caller :=
      certificate_real_smc_subroutine_has_matching_caller gen
    env_separated := certificate_real_smc_env_separated gen
    adv_separated := certificate_real_smc_adv_separated gen
    no_direct_environment_communication :=
      certificate_real_smc_no_direct_environment_communication gen
    adversary_communication_is_backdoor :=
      certificate_real_smc_adversary_communication_is_backdoor gen }

/-- 审计入口使用的 SMC 理想功能。 -/
noncomputable def certificate_ideal_smc_functionality :
    IdealFunctionality SMCEasyUCPayload :=
  IdealSMC certificate_smc_ids

/-- 两个 main machines 正是 SMC sender / receiver。 -/
theorem certificate_smc_sender_is_main
    (gen : PPTGroupGenerator) :
    (certificate_real_smc_protocol gen).is_main_machine cert_smc_sender_id := by
  refine ⟨⟨Unit, certificate_smc_sender_machine⟩, ?_, rfl, ?_⟩
  · simp [certificate_real_smc_protocol, certificate_real_smc_machines]
  · refine ⟨cert_sender_external_id, ?_, ?_, ?_⟩
    · simp [certificate_real_smc_protocol, certificate_real_smc_machines]
    · refine ⟨cert_smc_sender_to_external_port, ?_, rfl, rfl⟩
      simp [certificate_smc_sender_machine]
    · change cert_sender_external_id ∉ certificate_machine_id_list
      native_decide

theorem certificate_smc_receiver_is_main
    (gen : PPTGroupGenerator) :
    (certificate_real_smc_protocol gen).is_main_machine cert_smc_receiver_id := by
  refine ⟨⟨Unit, certificate_smc_receiver_machine⟩, ?_, rfl, ?_⟩
  · simp [certificate_real_smc_protocol, certificate_real_smc_machines]
  · refine ⟨cert_receiver_external_id, ?_, ?_, ?_⟩
    · simp [certificate_real_smc_protocol, certificate_real_smc_machines]
    · refine ⟨cert_smc_receiver_to_external_port, ?_, rfl, rfl⟩
      simp [certificate_smc_receiver_machine]
    · change cert_receiver_external_id ∉ certificate_machine_id_list
      native_decide

/-- Certificate 中的 UC 安全目标陈述。证明将在后续安全证明文件中完成。 -/
def certificate_smc_uc_realizes
    (gen : PPTGroupGenerator) : Prop :=
  ppt_ddh_assumption gen →
    UCRealizesComputational
      (certificate_real_smc_protocol gen)
      certificate_ideal_smc_functionality

end LeanCryptoProtocols.CaseStudy.SMCEasyUC

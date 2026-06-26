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

def smc_sender_id : MachineId := 10
def smc_receiver_id : MachineId := 11
def ke_sender_id : MachineId := 12
def ke_receiver_id : MachineId := 13
def forw_ke_forward_id : MachineId := 14
def forw_ke_return_id : MachineId := 15
def forw_smc_id : MachineId := 16
def ideal_smc_id : MachineId := 17
def sender_external_id : MachineId := 18
def receiver_external_id : MachineId := 19

/-- 审计入口中固定的 real-world machine identities。 -/
def machine_id_list : List MachineId :=
  [ smc_sender_id
  , smc_receiver_id
  , ke_sender_id
  , ke_receiver_id
  , forw_ke_forward_id
  , forw_ke_return_id
  , forw_smc_id
  ]

/-- 该 case study 中带有 adversarial control backdoor 的 forwarding functionalities。 -/
def forw_control_targets : Finset MachineId :=
  {forw_ke_forward_id, forw_ke_return_id, forw_smc_id}

theorem id_ne_of_decide {a b : MachineId} (h : decide (a ≠ b) = true) :
    a ≠ b := by
  exact of_decide_eq_true h

theorem smc_sender_ne_smc_receiver :
    smc_sender_id ≠ smc_receiver_id := by decide

theorem smc_sender_ne_ke_sender :
    smc_sender_id ≠ ke_sender_id := by decide

theorem smc_sender_ne_ke_receiver :
    smc_sender_id ≠ ke_receiver_id := by decide

theorem smc_sender_ne_forw_ke_forward :
    smc_sender_id ≠ forw_ke_forward_id := by decide

theorem smc_sender_ne_forw_ke_return :
    smc_sender_id ≠ forw_ke_return_id := by decide

theorem smc_sender_ne_forw_smc :
    smc_sender_id ≠ forw_smc_id := by decide

theorem smc_sender_ne_ideal_smc :
    smc_sender_id ≠ ideal_smc_id := by decide

theorem smc_receiver_ne_ke_sender :
    smc_receiver_id ≠ ke_sender_id := by decide

theorem smc_receiver_ne_ke_receiver :
    smc_receiver_id ≠ ke_receiver_id := by decide

theorem smc_receiver_ne_forw_ke_forward :
    smc_receiver_id ≠ forw_ke_forward_id := by decide

theorem smc_receiver_ne_forw_ke_return :
    smc_receiver_id ≠ forw_ke_return_id := by decide

theorem smc_receiver_ne_forw_smc :
    smc_receiver_id ≠ forw_smc_id := by decide

theorem smc_receiver_ne_ideal_smc :
    smc_receiver_id ≠ ideal_smc_id := by decide

theorem ke_sender_ne_ke_receiver :
    ke_sender_id ≠ ke_receiver_id := by decide

theorem ke_sender_ne_forw_ke_forward :
    ke_sender_id ≠ forw_ke_forward_id := by decide

theorem ke_sender_ne_forw_ke_return :
    ke_sender_id ≠ forw_ke_return_id := by decide

theorem ke_sender_ne_forw_smc :
    ke_sender_id ≠ forw_smc_id := by decide

theorem ke_receiver_ne_forw_ke_forward :
    ke_receiver_id ≠ forw_ke_forward_id := by decide

theorem ke_receiver_ne_forw_ke_return :
    ke_receiver_id ≠ forw_ke_return_id := by decide

theorem ke_receiver_ne_forw_smc :
    ke_receiver_id ≠ forw_smc_id := by decide

theorem forw_ke_forward_ne_forw_ke_return :
    forw_ke_forward_id ≠ forw_ke_return_id := by decide

theorem forw_ke_forward_ne_forw_smc :
    forw_ke_forward_id ≠ forw_smc_id := by decide

theorem forw_ke_return_ne_forw_smc :
    forw_ke_return_id ≠ forw_smc_id := by decide

theorem sender_external_ne_smc_sender :
    sender_external_id ≠ smc_sender_id := by decide

theorem sender_external_ne_smc_receiver :
    sender_external_id ≠ smc_receiver_id := by decide

theorem sender_external_ne_ke_sender :
    sender_external_id ≠ ke_sender_id := by decide

theorem sender_external_ne_ke_receiver :
    sender_external_id ≠ ke_receiver_id := by decide

theorem sender_external_ne_forw_ke_forward :
    sender_external_id ≠ forw_ke_forward_id := by decide

theorem sender_external_ne_forw_ke_return :
    sender_external_id ≠ forw_ke_return_id := by decide

theorem sender_external_ne_forw_smc :
    sender_external_id ≠ forw_smc_id := by decide

theorem sender_external_ne_ideal_smc :
    sender_external_id ≠ ideal_smc_id := by decide

theorem receiver_external_ne_smc_sender :
    receiver_external_id ≠ smc_sender_id := by decide

theorem receiver_external_ne_smc_receiver :
    receiver_external_id ≠ smc_receiver_id := by decide

theorem receiver_external_ne_ke_sender :
    receiver_external_id ≠ ke_sender_id := by decide

theorem receiver_external_ne_ke_receiver :
    receiver_external_id ≠ ke_receiver_id := by decide

theorem receiver_external_ne_forw_ke_forward :
    receiver_external_id ≠ forw_ke_forward_id := by decide

theorem receiver_external_ne_forw_ke_return :
    receiver_external_id ≠ forw_ke_return_id := by decide

theorem receiver_external_ne_forw_smc :
    receiver_external_id ≠ forw_smc_id := by decide

theorem receiver_external_ne_ideal_smc :
    receiver_external_id ≠ ideal_smc_id := by decide

theorem sender_external_ne_receiver_external :
    sender_external_id ≠ receiver_external_id := by decide

theorem smc_sender_separated :
    smc_sender_id ≠ env_id ∧ smc_sender_id ≠ adv_id := by decide

theorem smc_receiver_separated :
    smc_receiver_id ≠ env_id ∧ smc_receiver_id ≠ adv_id := by decide

theorem ke_sender_separated :
    ke_sender_id ≠ env_id ∧ ke_sender_id ≠ adv_id := by decide

theorem ke_receiver_separated :
    ke_receiver_id ≠ env_id ∧ ke_receiver_id ≠ adv_id := by decide

theorem forw_ke_forward_separated :
    forw_ke_forward_id ≠ env_id ∧ forw_ke_forward_id ≠ adv_id := by decide

theorem forw_ke_return_separated :
    forw_ke_return_id ≠ env_id ∧ forw_ke_return_id ≠ adv_id := by decide

theorem forw_smc_separated :
    forw_smc_id ≠ env_id ∧ forw_smc_id ≠ adv_id := by decide

theorem ideal_smc_separated :
    ideal_smc_id ≠ env_id ∧ ideal_smc_id ≠ adv_id := by decide

theorem sender_external_separated :
    sender_external_id ≠ env_id ∧ sender_external_id ≠ adv_id := by decide

theorem receiver_external_separated :
    receiver_external_id ≠ env_id ∧ receiver_external_id ≠ adv_id := by decide

/-! ## Functionality identities -/

def forw_ke_forward_ids : ForwIds where
  sender_id := ke_sender_id
  receiver_id := ke_receiver_id
  functionality_id := forw_ke_forward_id
  sender_external_id := smc_sender_id
  receiver_external_id := smc_receiver_id
  sender_ne_receiver := ke_sender_ne_ke_receiver
  sender_ne_functionality := ke_sender_ne_forw_ke_forward
  receiver_ne_functionality := ke_receiver_ne_forw_ke_forward
  sender_id_separated := ke_sender_separated
  receiver_id_separated := ke_receiver_separated
  functionality_separated := forw_ke_forward_separated
  sender_external_separated :=
    ⟨smc_sender_ne_ke_sender, smc_sender_ne_ke_receiver,
      smc_sender_ne_forw_ke_forward, smc_sender_separated.1,
      smc_sender_separated.2⟩
  receiver_external_separated :=
    ⟨smc_receiver_ne_ke_sender, smc_receiver_ne_ke_receiver,
      smc_receiver_ne_forw_ke_forward, smc_receiver_separated.1,
      smc_receiver_separated.2⟩

def forw_ke_return_ids : ForwIds where
  sender_id := ke_receiver_id
  receiver_id := ke_sender_id
  functionality_id := forw_ke_return_id
  sender_external_id := smc_receiver_id
  receiver_external_id := smc_sender_id
  sender_ne_receiver := ke_sender_ne_ke_receiver.symm
  sender_ne_functionality := ke_receiver_ne_forw_ke_return
  receiver_ne_functionality := ke_sender_ne_forw_ke_return
  sender_id_separated := ke_receiver_separated
  receiver_id_separated := ke_sender_separated
  functionality_separated := forw_ke_return_separated
  sender_external_separated :=
    ⟨smc_receiver_ne_ke_receiver, smc_receiver_ne_ke_sender,
      smc_receiver_ne_forw_ke_return, smc_receiver_separated.1,
      smc_receiver_separated.2⟩
  receiver_external_separated :=
    ⟨smc_sender_ne_ke_receiver, smc_sender_ne_ke_sender,
      smc_sender_ne_forw_ke_return, smc_sender_separated.1,
      smc_sender_separated.2⟩

def forw_smc_ids : ForwIds where
  sender_id := smc_sender_id
  receiver_id := smc_receiver_id
  functionality_id := forw_smc_id
  sender_external_id := sender_external_id
  receiver_external_id := receiver_external_id
  sender_ne_receiver := smc_sender_ne_smc_receiver
  sender_ne_functionality := smc_sender_ne_forw_smc
  receiver_ne_functionality := smc_receiver_ne_forw_smc
  sender_id_separated := smc_sender_separated
  receiver_id_separated := smc_receiver_separated
  functionality_separated := forw_smc_separated
  sender_external_separated :=
    ⟨sender_external_ne_smc_sender, sender_external_ne_smc_receiver,
      sender_external_ne_forw_smc, sender_external_separated.1,
      sender_external_separated.2⟩
  receiver_external_separated :=
    ⟨receiver_external_ne_smc_sender, receiver_external_ne_smc_receiver,
      receiver_external_ne_forw_smc, receiver_external_separated.1,
      receiver_external_separated.2⟩

def smc_ids : SMCIds where
  sender_id := smc_sender_id
  receiver_id := smc_receiver_id
  functionality_id := ideal_smc_id
  sender_external_id := sender_external_id
  receiver_external_id := receiver_external_id
  sender_ne_receiver := smc_sender_ne_smc_receiver
  sender_ne_functionality := smc_sender_ne_ideal_smc
  receiver_ne_functionality := smc_receiver_ne_ideal_smc
  sender_id_separated := smc_sender_separated
  receiver_id_separated := smc_receiver_separated
  functionality_separated := ideal_smc_separated
  sender_external_separated :=
    ⟨sender_external_ne_smc_sender, sender_external_ne_smc_receiver,
      sender_external_ne_ideal_smc, sender_external_separated.1,
      sender_external_separated.2⟩
  receiver_external_separated :=
    ⟨receiver_external_ne_smc_sender, receiver_external_ne_smc_receiver,
      receiver_external_ne_ideal_smc, receiver_external_separated.1,
      receiver_external_separated.2⟩

/-! ## Ports used by the real protocol -/

def smc_sender_to_ke_sender_port : CommPort :=
  mk_input_port smc_sender_id ke_sender_id
    smc_sender_ne_ke_sender
    smc_sender_separated.2
    ke_sender_separated.2

def smc_sender_to_forw_smc_port : CommPort :=
  mk_input_port smc_sender_id forw_smc_id
    smc_sender_ne_forw_smc
    smc_sender_separated.2
    forw_smc_separated.2

def smc_sender_to_external_port : CommPort :=
  mk_subroutine_output_port smc_sender_id sender_external_id
    sender_external_ne_smc_sender.symm
    smc_sender_separated.2
    sender_external_separated.2

def smc_receiver_to_ke_receiver_port : CommPort :=
  mk_input_port smc_receiver_id ke_receiver_id
    smc_receiver_ne_ke_receiver
    smc_receiver_separated.2
    ke_receiver_separated.2

def smc_receiver_to_forw_smc_port : CommPort :=
  mk_input_port smc_receiver_id forw_smc_id
    smc_receiver_ne_forw_smc
    smc_receiver_separated.2
    forw_smc_separated.2

def smc_receiver_to_external_port : CommPort :=
  mk_subroutine_output_port smc_receiver_id receiver_external_id
    receiver_external_ne_smc_receiver.symm
    smc_receiver_separated.2
    receiver_external_separated.2

def ke_sender_to_smc_sender_port : CommPort :=
  mk_subroutine_output_port ke_sender_id smc_sender_id
    smc_sender_ne_ke_sender.symm
    ke_sender_separated.2
    smc_sender_separated.2

def ke_sender_to_forw_ke_forward_port : CommPort :=
  mk_input_port ke_sender_id forw_ke_forward_id
    ke_sender_ne_forw_ke_forward
    ke_sender_separated.2
    forw_ke_forward_separated.2

def ke_sender_to_forw_ke_return_port : CommPort :=
  mk_input_port ke_sender_id forw_ke_return_id
    ke_sender_ne_forw_ke_return
    ke_sender_separated.2
    forw_ke_return_separated.2

def ke_receiver_to_smc_receiver_port : CommPort :=
  mk_subroutine_output_port ke_receiver_id smc_receiver_id
    smc_receiver_ne_ke_receiver.symm
    ke_receiver_separated.2
    smc_receiver_separated.2

def ke_receiver_to_forw_ke_forward_port : CommPort :=
  mk_input_port ke_receiver_id forw_ke_forward_id
    ke_receiver_ne_forw_ke_forward
    ke_receiver_separated.2
    forw_ke_forward_separated.2

def ke_receiver_to_forw_ke_return_port : CommPort :=
  mk_input_port ke_receiver_id forw_ke_return_id
    ke_receiver_ne_forw_ke_return
    ke_receiver_separated.2
    forw_ke_return_separated.2

/-! ## Local programs -/

private noncomputable def option_resume {State : Type}
    (get : State → Option (Envelope SMCEasyUCPayload))
    (clear : State → State)
    (st : State) : PMF (ActivationResult SMCEasyUCPayload State) :=
  match get st with
  | none =>
      PMF.pure {
        state := st
        outgoing? := none
      }
  | some env =>
      PMF.pure {
        state := clear st
        outgoing? := some env
      }

def lookup_key : List (Sid × SharedKey) → Sid → SharedKey
  | [], _ => default_shared_key
  | (sid', key) :: rest, sid =>
      if sid' = sid then key else lookup_key rest sid

def insert_key_if_absent
    (keys : List (Sid × SharedKey)) (sid : Sid) (key : SharedKey) :
    List (Sid × SharedKey) :=
  match keys with
  | [] => [(sid, key)]
  | (sid', key') :: rest =>
      if sid' = sid then
        (sid', key') :: rest
      else
        (sid', key') :: insert_key_if_absent rest sid key

noncomputable def sample_public_group_element
    (gen : GroupGenerator) (n : ℕ) : PMF GroupElement :=
  (gen n).bind fun G =>
    G.sample_exponent.bind fun a =>
      PMF.pure ⟨G.encode (G.pow G.generator a)⟩

structure SMCSenderState where
  waiting_message : Option (Sid × Plaintext)
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

structure SMCReceiverState where
  session_key : Option SharedKey
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

inductive KESenderAction where
  | send_first
  | output_key (peer_share : GroupElement)

structure KESenderState where
  sec_param : ℕ
  local_share : Option GroupElement
  pending_action : Option KESenderAction

structure KEReceiverState where
  sec_param : ℕ
  pending_action : Option GroupElement
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

def ke_sender_init (n : ℕ) : KESenderState := {
  sec_param := n
  local_share := none
  pending_action := none
}

def ke_receiver_init (n : ℕ) : KEReceiverState := {
  sec_param := n
  pending_action := none
  pending_outgoing := none
}

def smc_sender_receive (st : SMCSenderState)
    (msg : Message SMCEasyUCPayload) : SMCSenderState :=
  match msg.payload with
  | .smc (.send sid plaintext) =>
      { waiting_message := some (sid, plaintext)
        pending_outgoing := some {
          port := smc_sender_to_ke_sender_port
          message := {
            source := some smc_sender_id
            label := .input
            payload := .ke .init
          }
          label_matches := rfl
        } }
  | .ke (.key shared_key) =>
      match st.waiting_message with
      | some (sid', plaintext) =>
          { waiting_message := none
            pending_outgoing := some {
              port := smc_sender_to_forw_smc_port
              message := {
                source := some smc_sender_id
                label := .input
                payload := .forw
                  (.submit smc_sender_id smc_receiver_id
                    (.smc_cipher sid' (enc shared_key plaintext)))
              }
              label_matches := rfl
            } }
      | none =>
          st
  | _ =>
      st

def smc_receiver_receive (st : SMCReceiverState)
    (msg : Message SMCEasyUCPayload) : SMCReceiverState :=
  match msg.payload with
  | .ke (.key shared_key) =>
      { session_key := some shared_key
        pending_outgoing := none }
  | .forw (.delivered _ _ (.smc_cipher sid cipher)) =>
      let shared_key := st.session_key.getD default_shared_key
      { st with
        pending_outgoing := some {
          port := smc_receiver_to_external_port
          message := {
            source := some smc_receiver_id
            label := .subroutineOutput
            payload := .smc (.received sid (dec shared_key cipher))
          }
          label_matches := rfl
        } }
  | _ =>
      st

def ke_sender_receive (st : KESenderState)
    (msg : Message SMCEasyUCPayload) : KESenderState :=
  match msg.payload with
  | .ke .init =>
      { st with pending_action := some .send_first }
  | .forw (.delivered _ _ (.ke_second share)) =>
      { st with pending_action := some (.output_key share) }
  | _ =>
      st

def ke_receiver_receive (st : KEReceiverState)
    (msg : Message SMCEasyUCPayload) : KEReceiverState :=
  match msg.payload with
  | .forw (.delivered _ _ (.ke_first share)) =>
      { st with pending_action := some share }
  | _ =>
      st

private def ke_sender_key_envelope
    (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := ke_sender_to_smc_sender_port
    message := {
      source := some ke_sender_id
      label := .subroutineOutput
      payload := .ke (.key shared_key)
    }
    label_matches := rfl
  }

private def ke_receiver_key_envelope
    (shared_key : SharedKey) :
    Envelope SMCEasyUCPayload :=
  { port := ke_receiver_to_smc_receiver_port
    message := {
      source := some ke_receiver_id
      label := .subroutineOutput
      payload := .ke (.key shared_key)
    }
    label_matches := rfl
  }

noncomputable def ke_sender_resume
    (gen : GroupGenerator)
    (st : KESenderState) : PMF (ActivationResult SMCEasyUCPayload KESenderState) :=
  match st.pending_action with
  | none =>
      PMF.pure {
        state := st
        outgoing? := none
      }
  | some .send_first =>
      sample_public_group_element gen st.sec_param |>.bind fun share =>
        PMF.pure {
          state := { st with local_share := some share, pending_action := none }
          outgoing? := some {
            port := ke_sender_to_forw_ke_forward_port
            message := {
              source := some ke_sender_id
              label := .input
              payload := .forw
                (.submit ke_sender_id ke_receiver_id (.ke_first share))
            }
            label_matches := rfl
          }
        }
  | some (.output_key peer_share) =>
      let shared_key :=
        match st.local_share with
        | some share => derive_shared_key share peer_share
        | none => default_shared_key
      PMF.pure {
        state := { st with local_share := none, pending_action := none }
        outgoing? := some (ke_sender_key_envelope shared_key)
      }

noncomputable def ke_receiver_resume
    (gen : GroupGenerator)
    (st : KEReceiverState) :
    PMF (ActivationResult SMCEasyUCPayload KEReceiverState) :=
  match st.pending_outgoing with
  | some env =>
      PMF.pure {
        state := { st with pending_outgoing := none }
        outgoing? := some env
      }
  | none =>
      match st.pending_action with
      | none =>
          PMF.pure {
            state := st
            outgoing? := none
          }
      | some peer_share =>
          sample_public_group_element gen st.sec_param |>.bind fun share =>
            let shared_key := derive_shared_key peer_share share
            PMF.pure {
              state := {
                st with
                  pending_action := none
                  pending_outgoing := some (ke_receiver_key_envelope shared_key)
              }
              outgoing? := some {
                port := ke_receiver_to_forw_ke_return_port
                message := {
                  source := some ke_receiver_id
                  label := .input
                  payload := .forw
                    (.submit ke_receiver_id ke_sender_id
                      (.ke_second share))
                }
                label_matches := rfl
              }
            }

noncomputable def smc_sender_program :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := SMCSenderState
  init := fun _ => { waiting_message := none, pending_outgoing := none }
  activate := fun st incoming? =>
    let st' :=
      match incoming? with
      | none => st
      | some msg =>
          match msg.payload with
          | .smc (.send sid plaintext) =>
              { waiting_message := some (sid, plaintext)
                pending_outgoing := some {
                  port := smc_sender_to_ke_sender_port
                  message := {
                    source := some smc_sender_id
                    label := .input
                    payload := .ke .init
                  }
                  label_matches := rfl
                } }
          | .ke (.key shared_key) =>
              match st.waiting_message with
              | some (sid', plaintext) =>
                  { waiting_message := none
                    pending_outgoing := some {
                      port := smc_sender_to_forw_smc_port
                      message := {
                        source := some smc_sender_id
                        label := .input
                        payload := .forw
                          (.submit smc_sender_id smc_receiver_id
                            (.smc_cipher sid' (enc shared_key plaintext)))
                      }
                      label_matches := rfl
                    } }
              | none =>
                  st
          | _ =>
              st
    match st'.pending_outgoing with
    | none =>
        PMF.pure {
          state := st'
          outgoing? := none
        }
    | some env =>
        PMF.pure {
          state := { st' with pending_outgoing := none }
          outgoing? := some env
        }
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def smc_receiver_program :
    MachineProgram SMCEasyUCPayload Unit where
  LocalState := SMCReceiverState
  init := fun _ => { session_key := none, pending_outgoing := none }
  activate := fun st incoming? =>
    let st' :=
      match incoming? with
      | none => st
      | some msg =>
          match msg.payload with
          | .ke (.key shared_key) =>
              { session_key := some shared_key
                pending_outgoing := none }
          | .forw (.delivered _ _ (.smc_cipher sid cipher)) =>
              let shared_key := st.session_key.getD default_shared_key
              { st with
                pending_outgoing := some {
                  port := smc_receiver_to_external_port
                  message := {
                    source := some smc_receiver_id
                    label := .subroutineOutput
                    payload := .smc (.received sid (dec shared_key cipher))
                  }
                  label_matches := rfl
                } }
          | _ =>
              st
    match st'.pending_outgoing with
    | none =>
        PMF.pure {
          state := st'
          outgoing? := none
        }
    | some env =>
        PMF.pure {
          state := { st' with pending_outgoing := none }
          outgoing? := some env
        }
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def ke_sender_program
    (gen : GroupGenerator) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := KESenderState
  init := ke_sender_init
  activate := fun st incoming? =>
    let st' :=
      match incoming? with
      | none => st
      | some msg =>
          match msg.payload with
          | .ke .init =>
              { st with pending_action := some .send_first }
          | .forw (.delivered _ _ (.ke_second share)) =>
              { st with pending_action := some (.output_key share) }
          | _ =>
              st
    match st'.pending_action with
    | none =>
        PMF.pure {
          state := st'
          outgoing? := none
        }
    | some .send_first =>
        sample_public_group_element gen st'.sec_param |>.bind fun share =>
          PMF.pure {
            state := { st' with local_share := some share, pending_action := none }
            outgoing? := some {
              port := ke_sender_to_forw_ke_forward_port
              message := {
                source := some ke_sender_id
                label := .input
                payload := .forw
                  (.submit ke_sender_id ke_receiver_id (.ke_first share))
              }
              label_matches := rfl
            }
          }
    | some (.output_key peer_share) =>
        let shared_key :=
          match st'.local_share with
          | some share => derive_shared_key share peer_share
          | none => default_shared_key
        PMF.pure {
          state := { st' with local_share := none, pending_action := none }
          outgoing? := some (ke_sender_key_envelope shared_key)
        }
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def ke_receiver_program
    (gen : GroupGenerator) : MachineProgram SMCEasyUCPayload Unit where
  LocalState := KEReceiverState
  init := ke_receiver_init
  activate := fun st incoming? =>
    let st' :=
      match incoming? with
      | none => st
      | some msg =>
          match msg.payload with
          | .forw (.delivered _ _ (.ke_first share)) =>
              { st with pending_action := some share }
          | _ =>
              st
    match st'.pending_outgoing with
    | some env =>
        PMF.pure {
          state := { st' with pending_outgoing := none }
          outgoing? := some env
        }
    | none =>
        match st'.pending_action with
        | none =>
            PMF.pure {
              state := st'
              outgoing? := none
            }
        | some peer_share =>
            sample_public_group_element gen st'.sec_param |>.bind fun share =>
              let shared_key := derive_shared_key peer_share share
              PMF.pure {
                state := {
                  st' with
                    pending_action := none
                    pending_outgoing := some (ke_receiver_key_envelope shared_key)
                }
                outgoing? := some {
                  port := ke_receiver_to_forw_ke_return_port
                  message := {
                    source := some ke_receiver_id
                    label := .input
                    payload := .forw
                      (.submit ke_receiver_id ke_sender_id
                        (.ke_second share))
                  }
                  label_matches := rfl
                }
              }
  is_halted := fun _ => false
  output := fun _ => ()

/-- 审计入口使用的 SMC 理想功能。 -/
noncomputable def ideal_smc_functionality :
    IdealFunctionality SMCEasyUCPayload :=
  IdealSMC smc_ids

end LeanCryptoProtocols.CaseStudy.SMCEasyUC

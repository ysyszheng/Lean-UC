import LeanCryptoProtocols.UC.Functionality.SMCCommon

/-!
# EasyUC case study 中的理想 `SMC`

这里的理想 secure message communication functionality 很简单：

- sender 输入一条明文；
- functionality 把同一条明文交给 receiver。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- `SMC` 参与方与功能机的统一命名。 -/
structure SMCIds where
  sender_id : MachineId
  receiver_id : MachineId
  functionality_id : MachineId
  sender_external_id : MachineId
  receiver_external_id : MachineId
  sender_ne_receiver : sender_id ≠ receiver_id
  sender_ne_functionality : sender_id ≠ functionality_id
  receiver_ne_functionality : receiver_id ≠ functionality_id
  sender_id_separated : sender_id ≠ env_id ∧ sender_id ≠ adv_id
  receiver_id_separated : receiver_id ≠ env_id ∧ receiver_id ≠ adv_id
  functionality_separated : functionality_id ≠ env_id ∧ functionality_id ≠ adv_id
  sender_external_separated :
    sender_external_id ≠ sender_id ∧
      sender_external_id ≠ receiver_id ∧
      sender_external_id ≠ functionality_id ∧
      sender_external_id ≠ env_id ∧
      sender_external_id ≠ adv_id
  receiver_external_separated :
    receiver_external_id ≠ sender_id ∧
      receiver_external_id ≠ receiver_id ∧
      receiver_external_id ≠ functionality_id ∧
      receiver_external_id ≠ env_id ∧
      receiver_external_id ≠ adv_id

def smc_sender_port (ids : SMCIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.sender_id
    (by simpa [Ne, eq_comm] using ids.sender_ne_functionality.symm)
    ids.functionality_separated.2
    ids.sender_id_separated.2

def smc_receiver_port (ids : SMCIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.receiver_id
    (by simpa [Ne, eq_comm] using ids.receiver_ne_functionality.symm)
    ids.functionality_separated.2
    ids.receiver_id_separated.2

def smc_adversary_port (ids : SMCIds) : CommPort :=
  mk_backdoor_port
    ids.functionality_id
    adv_id
    ids.functionality_separated.2
    (Or.inr rfl)

namespace SMCImpl

structure PendingMessage where
  sid : Sid
  sender_id : MachineId
  receiver_id : MachineId
  plaintext : Plaintext
  deriving Repr, DecidableEq

inductive Phase where
  | sstate1
  | sstate2 (msg : PendingMessage)
  | sstate3
  deriving Repr, DecidableEq

structure State where
  phase : Phase
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

def init_state : State := {
  phase := .sstate1
  pending_outgoing := none
}

def build_observe_envelope (ids : SMCIds) (msg : PendingMessage) :
    Envelope SMCEasyUCPayload := {
  port := smc_adversary_port ids
  message := {
    source := some ids.functionality_id
    label := .backdoor
    payload := .smc_plain (.observe msg.sid msg.sender_id msg.receiver_id)
  }
  label_matches := rfl
}

def build_deliver_envelope (ids : SMCIds) (msg : PendingMessage) :
    Envelope SMCEasyUCPayload := {
  port := smc_receiver_port ids
  message := {
    source := some ids.functionality_id
    label := .subroutineOutput
    payload := .smc_from_functionality ids.receiver_external_id
      (.received msg.sid msg.plaintext)
  }
  label_matches := rfl
}

def receive_send (ids : SMCIds) (sid : Sid) (plaintext : Plaintext) : State :=
  let pending_msg : PendingMessage := {
    sid := sid
    sender_id := ids.sender_external_id
    receiver_id := ids.receiver_external_id
    plaintext := plaintext
  }
  { phase := .sstate2 pending_msg
    pending_outgoing := some (build_observe_envelope ids pending_msg) }

def receive_release (ids : SMCIds) (st : State)
    (pending_msg : PendingMessage) (sid : Sid) : State :=
  if sid = pending_msg.sid then
    { phase := .sstate3
      pending_outgoing := some (build_deliver_envelope ids pending_msg) }
  else
    st

def receive (ids : SMCIds) (st : State) (msg : Message SMCEasyUCPayload) :
    State :=
  match st.phase, msg.source, msg.label, msg.payload with
  | .sstate1, some src, .input, .smc_plain (.send sid plaintext) =>
      if _h_src : src = ids.sender_id then
        receive_send ids sid plaintext
      else
        st
  | .sstate1, _, .input, .smc_to_functionality caller_source (.send sid plaintext) =>
      if _h_src : caller_source = some ids.sender_external_id then
        receive_send ids sid plaintext
      else
        st
  | .sstate2 pending_msg, some src, .backdoor, .smc_plain (.release sid) =>
      if _h_src : src = adv_id then
        receive_release ids st pending_msg sid
      else
        st
  | _, _, _, _ =>
      st

noncomputable def resume (st : State) : PMF (ActivationResult SMCEasyUCPayload State) :=
  match st.pending_outgoing with
  | none =>
      PMF.pure {
        state := st
        outgoing? := none
      }
  | some envelope =>
      PMF.pure {
        state := { st with pending_outgoing := none }
        outgoing? := some envelope
      }

def communication_set (ids : SMCIds) : Finset CommPort :=
  { smc_sender_port ids, smc_receiver_port ids, smc_adversary_port ids }

theorem receive_send_sets_pending
    (ids : SMCIds)
    (sid : Sid)
    (plaintext : Plaintext) :
    receive ids init_state
      { source := some ids.sender_id
        label := .input
        payload := .smc_plain (.send sid plaintext) } =
      receive_send ids sid plaintext := by
  simp [receive, init_state]

theorem receive_to_functionality_sets_pending
    (ids : SMCIds)
    (sid : Sid)
    (plaintext : Plaintext) :
    receive ids init_state
      { source := some ids.sender_id
        label := .input
        payload := .smc_to_functionality (some ids.sender_external_id)
          (.send sid plaintext) } =
      receive_send ids sid plaintext := by
  simp [receive, init_state]

theorem resume_init_state_none :
    resume init_state =
      PMF.pure {
        state := init_state
        outgoing? := none
      } := by
  simp [resume, init_state]

theorem resume_pending_some
    (ids : SMCIds)
    (sid : Sid)
    (plaintext : Plaintext) :
    resume
      { phase := .sstate3
        pending_outgoing := some {
          port := smc_receiver_port ids
          message := {
            source := some ids.functionality_id
            label := .subroutineOutput
            payload := .smc_from_functionality ids.receiver_external_id (.received sid plaintext)
          }
          label_matches := rfl
        } } =
      PMF.pure {
        state := {
          phase := .sstate3
          pending_outgoing := none
        }
        outgoing? := some {
          port := smc_receiver_port ids
          message := {
            source := some ids.functionality_id
            label := .subroutineOutput
            payload := .smc_from_functionality ids.receiver_external_id (.received sid plaintext)
          }
          label_matches := rfl
        }
      } := by
  simp [resume]

noncomputable def machine (ids : SMCIds) : Machine SMCEasyUCPayload Unit where
  id := ids.functionality_id
  communication_set := communication_set ids
  program := {
    LocalState := State
    init := fun _ => init_state
    receive := receive ids
    resume := resume
    is_halted := fun _ => false
    output := fun _ => ()
  }
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [communication_set] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [communication_set] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (ids.sender_ne_receiver h_dest).elim
      · exact (ids.sender_id_separated.2 h_dest).elim
      · exact (ids.sender_ne_receiver h_dest.symm).elim
      · rfl
      · exact (ids.receiver_id_separated.2 h_dest).elim
      · exact (ids.sender_id_separated.2 h_dest.symm).elim
      · exact (ids.receiver_id_separated.2 h_dest.symm).elim
      · rfl

end SMCImpl

private def smc_party_external_ids (ids : SMCIds) (pid : MachineId) : Finset MachineId :=
  if pid = ids.sender_id then
    {ids.sender_external_id}
  else if pid = ids.receiver_id then
    {ids.receiver_external_id}
  else
    ∅

/-- EasyUC case study 的理想 SMC functionality。 -/
noncomputable def IdealSMC : SMCIds → IdealFunctionality SMCEasyUCPayload
  | ids => {
      party_ids := [ids.sender_id, ids.receiver_id]
      functionality_id := ids.functionality_id
      machine := SMCImpl.machine ids
      id_matches := rfl
      party_ids_nodup := by
        simp [ids.sender_ne_receiver]
      parties_separated := by
        constructor
        · intro h
          simp at h
          rcases h with h | h
          · exact ids.sender_id_separated.1 h.symm
          · exact ids.receiver_id_separated.1 h.symm
        · intro h
          simp at h
          rcases h with h | h
          · exact ids.sender_id_separated.2 h.symm
          · exact ids.receiver_id_separated.2 h.symm
      functionality_separated := ids.functionality_separated
      functionality_not_party := by
        intro h
        simp at h
        rcases h with h | h
        · exact ids.sender_ne_functionality h.symm
        · exact ids.receiver_ne_functionality h.symm
      party_external_ids := smc_party_external_ids ids
      external_ids_nonempty := by
        intro pid h_pid
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [smc_party_external_ids]
        · simp [smc_party_external_ids, ids.sender_ne_receiver.symm]
      external_ids_outside_parties := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [smc_party_external_ids] at h_ext
          rcases h_ext with rfl
          simp [ids.sender_external_separated.1, ids.sender_external_separated.2.1]
        · simp [smc_party_external_ids, ids.sender_ne_receiver.symm] at h_ext
          rcases h_ext with rfl
          simp [ids.receiver_external_separated.1, ids.receiver_external_separated.2.1]
      external_ids_separated := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [smc_party_external_ids] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.sender_external_separated.2.2.1,
            ids.sender_external_separated.2.2.2.1,
            ids.sender_external_separated.2.2.2.2⟩
        · simp [smc_party_external_ids, ids.sender_ne_receiver.symm] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.receiver_external_separated.2.2.1,
            ids.receiver_external_separated.2.2.2.1,
            ids.receiver_external_separated.2.2.2.2⟩
      dummy_local_state := Option (Message SMCEasyUCPayload)
      dummy_init := fun _ => none
      dummy_receive := fun _ msg => some msg
      dummy_pending := fun st => st
      dummy_clear := fun _ => none
      wrap_input := fun caller_source payload =>
        match payload with
        | .smc_plain body => .smc_to_functionality caller_source body
        | other => other
      unwrap_output := fun payload =>
        match payload with
        | .smc_from_functionality dest body => some (dest, .smc_plain body)
        | _ => none
      functionality_ports_to_parties := by
        intro pid h_pid
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · refine ⟨smc_sender_port ids, ?_, rfl, rfl⟩
          change smc_sender_port ids ∈
            ({smc_sender_port ids, smc_receiver_port ids, smc_adversary_port ids} :
              Finset CommPort)
          simp
        · refine ⟨smc_receiver_port ids, ?_, rfl, rfl⟩
          change smc_receiver_port ids ∈
            ({smc_sender_port ids, smc_receiver_port ids, smc_adversary_port ids} :
              Finset CommPort)
          simp
      functionality_comm_constraints := by
        intro p hp
        have hp' :
            p = smc_sender_port ids ∨
              p = smc_receiver_port ids ∨
              p = smc_adversary_port ids := by
          change p ∈
            ({smc_sender_port ids, smc_receiver_port ids, smc_adversary_port ids} :
              Finset CommPort) at hp
          simpa [ids.sender_ne_receiver] using hp
        rcases hp' with rfl | rfl | rfl
        · refine Or.inl ⟨?_, rfl⟩
          change ids.sender_id ∈ ([ids.sender_id, ids.receiver_id] : List MachineId).toFinset
          simp
        · refine Or.inl ⟨?_, rfl⟩
          change ids.receiver_id ∈ ([ids.sender_id, ids.receiver_id] : List MachineId).toFinset
          simp
        · exact Or.inr ⟨rfl, rfl⟩
    }

theorem ideal_smc_sender_external_ids (ids : SMCIds) :
    (IdealSMC ids).party_external_ids ids.sender_id = {ids.sender_external_id} := by
  simp [IdealSMC, smc_party_external_ids]

theorem ideal_smc_receiver_external_ids (ids : SMCIds) :
    (IdealSMC ids).party_external_ids ids.receiver_id = {ids.receiver_external_id} := by
  simp [IdealSMC, smc_party_external_ids, ids.sender_ne_receiver.symm]

end LeanCryptoProtocols.UC.Functionality

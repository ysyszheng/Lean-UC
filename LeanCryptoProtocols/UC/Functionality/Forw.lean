import LeanCryptoProtocols.UC.Functionality.SMCCommon

/-!
# EasyUC case study 中的 `Forw`

`Forw` 是一个对 adversary 可见的 forwarding functionality：

- sender 向 `Forw` 提交网络消息；
- `Forw` 通过 backdoor 把可见事件暴露给 adversary；
- adversary 发出 `release` 后，`Forw` 把消息交付给 receiver。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- `Forw` 的参与方与 adversary 可见端口的统一命名。 -/
structure ForwIds where
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

/-- `Forw` 发往 sender dummy 的端口。当前只为接口完整性保留。 -/
def forw_sender_port (ids : ForwIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.sender_id
    (by simpa [Ne, eq_comm] using ids.sender_ne_functionality.symm)
    ids.functionality_separated.2
    ids.sender_id_separated.2

/-- `Forw` 发往 receiver dummy 的端口。 -/
def forw_receiver_port (ids : ForwIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.receiver_id
    (by simpa [Ne, eq_comm] using ids.receiver_ne_functionality.symm)
    ids.functionality_separated.2
    ids.receiver_id_separated.2

/-- `Forw` 发往 adversary 的 backdoor 端口。 -/
def forw_adversary_port (ids : ForwIds) : CommPort :=
  mk_backdoor_port
    ids.functionality_id
    adv_id
    ids.functionality_separated.2
    (Or.inr rfl)

namespace ForwImpl

structure PendingMessage where
  sender_id : MachineId
  receiver_id : MachineId
  payload : NetworkBody
  deriving Repr, DecidableEq

inductive Phase where
  | fstate1
  | fstate2 (msg : PendingMessage)
  | fstate3
  deriving Repr, DecidableEq

structure State where
  phase : Phase
  pending_outgoing : Option (Envelope SMCEasyUCPayload)
  deriving Repr, DecidableEq

def init_state : State := {
  phase := .fstate1
  pending_outgoing := none
}

def build_observe_envelope (ids : ForwIds) (msg : PendingMessage) :
    Envelope SMCEasyUCPayload := {
  port := forw_adversary_port ids
  message := {
    label := .backdoor
    payload := .forw (.observe msg.sender_id msg.receiver_id msg.payload)
  }
  label_matches := rfl
}

def build_deliver_envelope (ids : ForwIds) (msg : PendingMessage) :
    Envelope SMCEasyUCPayload := {
  port := forw_receiver_port ids
  message := {
    label := .subroutineOutput
    instruction := .dummyDestination ids.receiver_external_id
    payload := .forw (.delivered msg.sender_id msg.receiver_id msg.payload)
    instruction_valid := by
      refine ⟨?_, ?_, ?_⟩
      · intro pid h
        cases h
      · intro caller_id h
        cases h
      · intro dest_id h
        cases h
        rfl
  }
  label_matches := rfl
}

def receive_submit (ids : ForwIds)
    (sender_id receiver_id : MachineId) (payload : NetworkBody) : State :=
  let pending_msg : PendingMessage := {
    sender_id := sender_id
    receiver_id := receiver_id
    payload := payload
  }
  { phase := .fstate2 pending_msg
    pending_outgoing := some (build_observe_envelope ids pending_msg) }

def receive_release (ids : ForwIds) (_st : State)
    (pending_msg : PendingMessage) : State :=
  { phase := .fstate3
    pending_outgoing := some (build_deliver_envelope ids pending_msg) }

noncomputable def activate (ids : ForwIds) (st : State)
    (incoming? : Option (Message SMCEasyUCPayload)) :
    PMF (ActivationResult SMCEasyUCPayload State) :=
  let st' :=
    match incoming? with
    | none => st
    | some msg =>
        match st.phase, msg.source, msg.label, msg.instruction, msg.payload with
        | .fstate1, some src, .input, .plain, .forw (.submit sender_id receiver_id payload) =>
            if _h_src : src = sender_id then
              receive_submit ids sender_id receiver_id payload
            else
              st
        | .fstate1, _, .input, .dummyCaller caller_id,
            .forw (.submit sender_id receiver_id payload) =>
            if _h_src : caller_id = ids.sender_external_id then
              receive_submit ids sender_id receiver_id payload
            else
              st
        | .fstate2 pending_msg, some src, .backdoor, .plain, .forw .release =>
            if _h_src : src = adv_id then
              receive_release ids st pending_msg
            else
              st
        | _, _, _, _, _ =>
            st
  match st'.pending_outgoing with
  | none =>
      PMF.pure {
        state := st'
        outgoing? := none
      }
  | some envelope =>
      PMF.pure {
        state := { st' with pending_outgoing := none }
        outgoing? := some envelope
      }

def communication_set (ids : ForwIds) : Finset CommPort :=
  { forw_sender_port ids, forw_receiver_port ids, forw_adversary_port ids }

noncomputable def machine (ids : ForwIds) : Machine SMCEasyUCPayload Unit where
  id := ids.functionality_id
  communication_set := communication_set ids
  program := {
    LocalState := State
    init := fun _ => init_state
    activate := activate ids
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

end ForwImpl

private def forw_party_external_ids (ids : ForwIds) (pid : MachineId) : Finset MachineId :=
  if pid = ids.sender_id then
    {ids.sender_external_id}
  else if pid = ids.receiver_id then
    {ids.receiver_external_id}
  else
    ∅

/-- EasyUC case study 中的理想 forwarding functionality。 -/
noncomputable def IdealForw : ForwIds → IdealFunctionality SMCEasyUCPayload
  | ids => {
      party_ids := [ids.sender_id, ids.receiver_id]
      functionality_id := ids.functionality_id
      machine := ForwImpl.machine ids
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
      party_external_ids := forw_party_external_ids ids
      external_ids_nonempty := by
        intro pid h_pid
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [forw_party_external_ids]
        · simp [forw_party_external_ids, ids.sender_ne_receiver.symm]
      external_ids_outside_parties := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [forw_party_external_ids] at h_ext
          rcases h_ext with rfl
          simp [ids.sender_external_separated.1, ids.sender_external_separated.2.1]
        · simp [forw_party_external_ids, ids.sender_ne_receiver.symm] at h_ext
          rcases h_ext with rfl
          simp [ids.receiver_external_separated.1, ids.receiver_external_separated.2.1]
      external_ids_separated := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [forw_party_external_ids] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.sender_external_separated.2.2.1,
            ids.sender_external_separated.2.2.2.1,
            ids.sender_external_separated.2.2.2.2⟩
        · simp [forw_party_external_ids, ids.sender_ne_receiver.symm] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.receiver_external_separated.2.2.1,
            ids.receiver_external_separated.2.2.2.1,
            ids.receiver_external_separated.2.2.2.2⟩
      functionality_ports_to_parties := by
        intro pid h_pid
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · refine ⟨forw_sender_port ids, ?_, rfl, rfl⟩
          change forw_sender_port ids ∈
            ({ forw_sender_port ids, forw_receiver_port ids, forw_adversary_port ids } :
              Finset CommPort)
          simp
        · refine ⟨forw_receiver_port ids, ?_, rfl, rfl⟩
          change forw_receiver_port ids ∈
            ({ forw_sender_port ids, forw_receiver_port ids, forw_adversary_port ids } :
              Finset CommPort)
          simp
      functionality_comm_constraints := by
        intro p hp
        have hp' :
            p = forw_sender_port ids ∨
              p = forw_receiver_port ids ∨
              p = forw_adversary_port ids := by
          change p ∈
            ({ forw_sender_port ids, forw_receiver_port ids, forw_adversary_port ids } :
              Finset CommPort) at hp
          simp [ids.sender_ne_receiver] at hp
          exact hp
        rcases hp' with rfl | rfl | rfl
        · refine Or.inl ⟨?_, rfl⟩
          change ids.sender_id ∈ ([ids.sender_id, ids.receiver_id] : List MachineId).toFinset
          simp
        · refine Or.inl ⟨?_, rfl⟩
          change ids.receiver_id ∈ ([ids.sender_id, ids.receiver_id] : List MachineId).toFinset
          simp
        · exact Or.inr ⟨rfl, rfl⟩
    }

end LeanCryptoProtocols.UC.Functionality

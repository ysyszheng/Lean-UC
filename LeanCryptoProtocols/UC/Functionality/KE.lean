import LeanCryptoProtocols.UC.Functionality.SMCCommon

/-!
# EasyUC case study 中的 `KE`

本文件提供 SMC case study 需要的 key-exchange ideal functionality。
它按 EasyUC blueprint 中的五态理想 key-exchange functionality 建模：
两次 party 激活都先通知 adversary，收到 adversary approval 后才输出同一个密钥。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- `KE` 参与方与功能机的统一命名。 -/
structure KEIds where
  initiator_id : MachineId
  responder_id : MachineId
  functionality_id : MachineId
  initiator_external_id : MachineId
  responder_external_id : MachineId
  initiator_ne_responder : initiator_id ≠ responder_id
  initiator_ne_functionality : initiator_id ≠ functionality_id
  responder_ne_functionality : responder_id ≠ functionality_id
  initiator_id_separated : initiator_id ≠ env_id ∧ initiator_id ≠ adv_id
  responder_id_separated : responder_id ≠ env_id ∧ responder_id ≠ adv_id
  functionality_separated : functionality_id ≠ env_id ∧ functionality_id ≠ adv_id
  initiator_external_separated :
    initiator_external_id ≠ initiator_id ∧
      initiator_external_id ≠ responder_id ∧
      initiator_external_id ≠ functionality_id ∧
      initiator_external_id ≠ env_id ∧
      initiator_external_id ≠ adv_id
  responder_external_separated :
    responder_external_id ≠ initiator_id ∧
      responder_external_id ≠ responder_id ∧
      responder_external_id ≠ functionality_id ∧
      responder_external_id ≠ env_id ∧
      responder_external_id ≠ adv_id

/-- `KE` functionality 发往 initiator 的端口。 -/
def ke_initiator_port (ids : KEIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.initiator_id
    (by simpa [Ne, eq_comm] using ids.initiator_ne_functionality.symm)
    ids.functionality_separated.2
    ids.initiator_id_separated.2

/-- `KE` functionality 发往 responder 的端口。 -/
def ke_responder_port (ids : KEIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.responder_id
    (by simpa [Ne, eq_comm] using ids.responder_ne_functionality.symm)
    ids.functionality_separated.2
    ids.responder_id_separated.2

/-- `KE` functionality 发往 adversary 的 backdoor 端口。 -/
def ke_adversary_port (ids : KEIds) : CommPort :=
  mk_backdoor_port
    ids.functionality_id
    adv_id
    ids.functionality_separated.2
    (Or.inr rfl)

namespace KEImpl

abbrev SessionKey : Type := Sid × Ssid

inductive Phase where
  | kstate1
  | kstate2
      (sid : Sid)
      (ssid : Ssid)
      (initiator_id responder_id : MachineId)
  | kstate3
      (sid : Sid)
      (ssid : Ssid)
      (initiator_id responder_id : MachineId)
      (shared_key : SharedKey)
  | kstate4
      (sid : Sid)
      (ssid : Ssid)
      (initiator_id responder_id : MachineId)
      (shared_key : SharedKey)
  | kstate5
  deriving Repr, DecidableEq

structure State where
  phase : Phase
  pending_outgoing : Option (Envelope SMCEasyUCPayload)

def init_state : State := {
  phase := .kstate1
  pending_outgoing := none
}

def initialized? : List SessionKey → SessionKey → Bool
  | [], _ => false
  | key' :: rest, key => if key' = key then true else initialized? rest key

def confirmed? : List SessionKey → SessionKey → Bool
  | [], _ => false
  | key' :: rest, key => if key' = key then true else confirmed? rest key

def build_init_observe_envelope (ids : KEIds) (sid : Sid) (ssid : Ssid) :
    Envelope SMCEasyUCPayload :=
  { port := ke_adversary_port ids
    message := {
      source := some ids.functionality_id
      label := .backdoor
      payload := .ke_plain
        (.observe_init sid ssid ids.initiator_external_id ids.responder_external_id)
    }
    label_matches := rfl
  }

def build_confirm_observe_envelope (ids : KEIds) (sid : Sid) (ssid : Ssid) :
    Envelope SMCEasyUCPayload :=
  { port := ke_adversary_port ids
    message := {
      source := some ids.functionality_id
      label := .backdoor
      payload := .ke_plain (.observe_confirm sid ssid)
    }
    label_matches := rfl
  }

def build_initiator_key_envelope (ids : KEIds) (sid : Sid) (ssid : Ssid)
    (shared_key : SharedKey) : Envelope SMCEasyUCPayload :=
  { port := ke_initiator_port ids
    message := {
      source := some ids.functionality_id
      label := .subroutineOutput
      payload := .ke_from_functionality ids.initiator_external_id (.key sid ssid shared_key)
    }
    label_matches := rfl
  }

def build_responder_key_envelope (ids : KEIds) (sid : Sid) (ssid : Ssid)
    (shared_key : SharedKey) : Envelope SMCEasyUCPayload :=
  { port := ke_responder_port ids
    message := {
      source := some ids.functionality_id
      label := .subroutineOutput
      payload := .ke_from_functionality ids.responder_external_id (.key sid ssid shared_key)
    }
    label_matches := rfl
  }

def receive_init (ids : KEIds) (sid : Sid) (ssid : Ssid) : State :=
  { phase := .kstate2 sid ssid ids.initiator_external_id ids.responder_external_id
    pending_outgoing := some (build_init_observe_envelope ids sid ssid) }

def receive_release_init (ids : KEIds) (st : State)
    (sid ssid : Nat) (initiator_id responder_id : MachineId)
    (release_sid : Sid) (release_ssid : Ssid) : State :=
  if release_sid = sid ∧ release_ssid = ssid then
    let shared_key := default_shared_key
    { phase := .kstate3 sid ssid initiator_id responder_id shared_key
      pending_outgoing := some (build_responder_key_envelope ids sid ssid shared_key) }
  else
    st

def receive_confirm (ids : KEIds) (sid : Sid) (ssid : Ssid)
    (initiator_id responder_id : MachineId) (shared_key : SharedKey) : State :=
  { phase := .kstate4 sid ssid initiator_id responder_id shared_key
    pending_outgoing := some (build_confirm_observe_envelope ids sid ssid) }

def receive_release_confirm (ids : KEIds) (st : State)
    (sid ssid : Nat) (_initiator_id _responder_id : MachineId)
    (shared_key : SharedKey) (release_sid : Sid) (release_ssid : Ssid) : State :=
  if release_sid = sid ∧ release_ssid = ssid then
    { phase := .kstate5
      pending_outgoing := some (build_initiator_key_envelope ids sid ssid shared_key) }
  else
    st

def receive (ids : KEIds) (st : State) (msg : Message SMCEasyUCPayload) : State :=
  match st.phase, msg.source, msg.label, msg.payload with
  | .kstate1, some src, .input, .ke_plain (.init sid ssid) =>
      if _h_src : src = ids.initiator_id then receive_init ids sid ssid else st
  | .kstate1, _, .input, .ke_to_functionality caller_source (.init sid ssid) =>
      if _h_src : caller_source = some ids.initiator_external_id then
        receive_init ids sid ssid
      else
        st
  | .kstate2 sid ssid initiator_id responder_id, some src, .backdoor,
      .ke_plain (.release_init release_sid release_ssid) =>
      if _h_src : src = adv_id then
        receive_release_init ids st sid ssid initiator_id responder_id release_sid release_ssid
      else
        st
  | .kstate3 sid ssid initiator_id responder_id shared_key, some src, .input,
      .ke_plain (.confirm confirm_sid confirm_ssid) =>
      if _h_src : src = ids.responder_id ∧ confirm_sid = sid ∧ confirm_ssid = ssid then
        receive_confirm ids sid ssid initiator_id responder_id shared_key
      else
        st
  | .kstate3 sid ssid initiator_id responder_id shared_key, _, .input,
      .ke_to_functionality caller_source (.confirm confirm_sid confirm_ssid) =>
      if _h_src :
          caller_source = some ids.responder_external_id ∧
            confirm_sid = sid ∧
            confirm_ssid = ssid then
        receive_confirm ids sid ssid initiator_id responder_id shared_key
      else
        st
  | .kstate4 sid ssid initiator_id responder_id shared_key, some src, .backdoor,
      .ke_plain (.release_confirm release_sid release_ssid) =>
      if _h_src : src = adv_id then
        receive_release_confirm ids st sid ssid initiator_id responder_id shared_key
          release_sid release_ssid
      else
        st
  | _, _, _, _ => st

noncomputable def resume (st : State) : PMF (ActivationResult SMCEasyUCPayload State) :=
  match st.pending_outgoing with
  | none =>
      PMF.pure { state := st, outgoing? := none }
  | some envelope =>
      PMF.pure {
        state := { st with pending_outgoing := none }
        outgoing? := some envelope
      }

def communication_set (ids : KEIds) : Finset CommPort :=
  { ke_initiator_port ids, ke_responder_port ids, ke_adversary_port ids }

noncomputable def machine (ids : KEIds) : Machine SMCEasyUCPayload Unit where
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
      · exact (ids.initiator_ne_responder h_dest).elim
      · exact (ids.initiator_id_separated.2 h_dest).elim
      · exact (ids.initiator_ne_responder h_dest.symm).elim
      · rfl
      · exact (ids.responder_id_separated.2 h_dest).elim
      · exact (ids.initiator_id_separated.2 h_dest.symm).elim
      · exact (ids.responder_id_separated.2 h_dest.symm).elim
      · rfl

end KEImpl

private def ke_party_external_ids (ids : KEIds) (pid : MachineId) : Finset MachineId :=
  if pid = ids.initiator_id then
    {ids.initiator_external_id}
  else if pid = ids.responder_id then
    {ids.responder_external_id}
  else
    ∅

/-- case study 中的 ideal key exchange functionality。 -/
noncomputable def IdealKE : KEIds → IdealFunctionality SMCEasyUCPayload
  | ids => {
      party_ids := [ids.initiator_id, ids.responder_id]
      functionality_id := ids.functionality_id
      machine := KEImpl.machine ids
      id_matches := rfl
      party_ids_nodup := by
        simp [ids.initiator_ne_responder]
      parties_separated := by
        constructor
        · intro h
          simp at h
          rcases h with h | h
          · exact ids.initiator_id_separated.1 h.symm
          · exact ids.responder_id_separated.1 h.symm
        · intro h
          simp at h
          rcases h with h | h
          · exact ids.initiator_id_separated.2 h.symm
          · exact ids.responder_id_separated.2 h.symm
      functionality_separated := ids.functionality_separated
      functionality_not_party := by
        intro h
        simp at h
        rcases h with h | h
        · exact ids.initiator_ne_functionality h.symm
        · exact ids.responder_ne_functionality h.symm
      party_external_ids := ke_party_external_ids ids
      external_ids_nonempty := by
        intro pid h_pid
        have h_cases : pid = ids.initiator_id ∨ pid = ids.responder_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [ke_party_external_ids]
        · simp [ke_party_external_ids, ids.initiator_ne_responder.symm]
      external_ids_outside_parties := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.initiator_id ∨ pid = ids.responder_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [ke_party_external_ids] at h_ext
          rcases h_ext with rfl
          simp [ids.initiator_external_separated.1, ids.initiator_external_separated.2.1]
        · simp [ke_party_external_ids, ids.initiator_ne_responder.symm] at h_ext
          rcases h_ext with rfl
          simp [ids.responder_external_separated.1, ids.responder_external_separated.2.1]
      external_ids_separated := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.initiator_id ∨ pid = ids.responder_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [ke_party_external_ids] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.initiator_external_separated.2.2.1,
            ids.initiator_external_separated.2.2.2.1,
            ids.initiator_external_separated.2.2.2.2⟩
        · simp [ke_party_external_ids, ids.initiator_ne_responder.symm] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.responder_external_separated.2.2.1,
            ids.responder_external_separated.2.2.2.1,
            ids.responder_external_separated.2.2.2.2⟩
      dummy_local_state := Option (Message SMCEasyUCPayload)
      dummy_init := fun _ => none
      dummy_receive := fun _ msg => some msg
      dummy_pending := fun st => st
      dummy_clear := fun _ => none
      wrap_input := fun caller_source payload =>
        match payload with
        | .ke_plain body => .ke_to_functionality caller_source body
        | other => other
      unwrap_output := fun payload =>
        match payload with
        | .ke_from_functionality dest body => some (dest, .ke_plain body)
        | _ => none
      functionality_ports_to_parties := by
        intro pid h_pid
        have h_cases : pid = ids.initiator_id ∨ pid = ids.responder_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · refine ⟨ke_initiator_port ids, ?_, rfl, rfl⟩
          change ke_initiator_port ids ∈
            ({ke_initiator_port ids, ke_responder_port ids, ke_adversary_port ids} :
              Finset CommPort)
          simp
        · refine ⟨ke_responder_port ids, ?_, rfl, rfl⟩
          change ke_responder_port ids ∈
            ({ke_initiator_port ids, ke_responder_port ids, ke_adversary_port ids} :
              Finset CommPort)
          simp
      functionality_comm_constraints := by
        intro p hp
        have hp' :
            p = ke_initiator_port ids ∨
              p = ke_responder_port ids ∨
              p = ke_adversary_port ids := by
          change p ∈
            ({ke_initiator_port ids, ke_responder_port ids, ke_adversary_port ids} :
              Finset CommPort) at hp
          simpa [ids.initiator_ne_responder] using hp
        rcases hp' with rfl | rfl | rfl
        · refine Or.inl ⟨?_, rfl⟩
          change ids.initiator_id ∈ ([ids.initiator_id, ids.responder_id] : List MachineId).toFinset
          simp
        · refine Or.inl ⟨?_, rfl⟩
          change ids.responder_id ∈ ([ids.initiator_id, ids.responder_id] : List MachineId).toFinset
          simp
        · exact Or.inr ⟨rfl, rfl⟩
    }

theorem ideal_ke_initiator_external_ids (ids : KEIds) :
    (IdealKE ids).party_external_ids ids.initiator_id = {ids.initiator_external_id} := by
  simp [IdealKE, ke_party_external_ids]

theorem ideal_ke_responder_external_ids (ids : KEIds) :
    (IdealKE ids).party_external_ids ids.responder_id = {ids.responder_external_id} := by
  simp [IdealKE, ke_party_external_ids, ids.initiator_ne_responder.symm]

end LeanCryptoProtocols.UC.Functionality

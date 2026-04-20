import LeanCryptoProtocols.UC.Security

/-!
# 两方 1-out-of-2 OT 理想功能

本文件按新的 message-driven / controller-driven 接口，给出两方 bit OT 的理想功能。允许开多个 `call_id` 的调用 session。

这里：

- `F_OT` 只保留值语义；
- `IdealOT` 返回一个 `IdealFunctionality`；
- 具体的 ideal protocol 由 `mk_ideal_protocol` 自动从 `IdealOT` 生成。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- OT 发送方输入的两个 bit。 -/
structure OTSenderInput where
  m0 : Bool
  m1 : Bool
  deriving Repr, DecidableEq

/-- OT 接收方输入的选择位。 -/
abbrev OTReceiverInput : Type := Bool

/-- OT 接收方输出。 -/
abbrev OTOutput : Type := Bool

/-- 单次 OT 的值语义。 -/
def F_OT (sender : OTSenderInput) (choice : OTReceiverInput) : OTOutput :=
  cond choice sender.m1 sender.m0

@[simp] theorem F_OT_false (sender : OTSenderInput) :
    F_OT sender false = sender.m0 := by
  rfl

@[simp] theorem F_OT_true (sender : OTSenderInput) :
    F_OT sender true = sender.m1 := by
  rfl

/-- OT 的值语义正确性。 -/
theorem F_OT_correct (sender : OTSenderInput) (choice : Bool) :
    F_OT sender choice = cond choice sender.m1 sender.m0 := by
  rfl

/-- OT 的业务消息体。 -/
inductive OTBody where
  | sender_req (call_id : Nat) (sender : OTSenderInput)
  | receiver_req (call_id : Nat) (choice : OTReceiverInput)
  | receiver_resp (call_id : Nat) (out : OTOutput)
  deriving Repr, DecidableEq

/--
OT 理想世界里统一使用的 payload。

- `plain`：环境与 dummy party 之间的原始业务消息；
- `to_functionality`：dummy party 转发给功能机的消息，额外带上原始调用者 identity；
- `from_functionality`：功能机返回给 dummy party 的消息，额外带上目标 identity。
-/
inductive OTPayload where
  | plain (body : OTBody)
  | to_functionality (caller_source : Option MachineId) (body : OTBody)
  | from_functionality (destination : MachineId) (body : OTBody)
  deriving Repr, DecidableEq

/-- OT 两方与功能机、external identities 的统一命名。 -/
structure OTIds where
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

/-- OT 理想功能发往 sender dummy 的端口。 -/
def sender_port (ids : OTIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.sender_id
    (by simpa [Ne, eq_comm] using ids.sender_ne_functionality.symm)
    ids.functionality_separated.2
    ids.sender_id_separated.2

/-- OT 理想功能发往 receiver dummy 的端口。 -/
def receiver_port (ids : OTIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.receiver_id
    (by simpa [Ne, eq_comm] using ids.receiver_ne_functionality.symm)
    ids.functionality_separated.2
    ids.receiver_id_separated.2

namespace OTImpl

structure State where
  sender_reqs : List (Nat × OTSenderInput)
  receiver_reqs : List (Nat × OTReceiverInput)
  pending_outgoing : Option (Envelope OTPayload)

def init_state : State := {
  sender_reqs := []
  receiver_reqs := []
  pending_outgoing := none
}

def lookup_sender : List (Nat × OTSenderInput) → Nat → Option OTSenderInput
  | [], _ => none
  | (cid, sender) :: rest, call_id =>
      if cid = call_id then some sender else lookup_sender rest call_id

def lookup_receiver : List (Nat × OTReceiverInput) → Nat → Option OTReceiverInput
  | [], _ => none
  | (cid, choice) :: rest, call_id =>
      if cid = call_id then some choice else lookup_receiver rest call_id

def insert_sender_if_absent (reqs : List (Nat × OTSenderInput))
    (call_id : Nat) (sender : OTSenderInput) : List (Nat × OTSenderInput) :=
  if lookup_sender reqs call_id |>.isSome then reqs else (call_id, sender) :: reqs

def insert_receiver_if_absent (reqs : List (Nat × OTReceiverInput))
    (call_id : Nat) (choice : OTReceiverInput) : List (Nat × OTReceiverInput) :=
  if lookup_receiver reqs call_id |>.isSome then reqs else (call_id, choice) :: reqs

def remove_sender (reqs : List (Nat × OTSenderInput)) (call_id : Nat) :
    List (Nat × OTSenderInput) :=
  reqs.filter fun entry => entry.1 ≠ call_id

def remove_receiver (reqs : List (Nat × OTReceiverInput)) (call_id : Nat) :
    List (Nat × OTReceiverInput) :=
  reqs.filter fun entry => entry.1 ≠ call_id

def build_receiver_response (ids : OTIds)
    (call_id : Nat) (sender : OTSenderInput) (choice : OTReceiverInput) :
    Envelope OTPayload := {
  port := receiver_port ids
  message := {
    source := some ids.functionality_id
    label := .subroutineOutput
    payload := .from_functionality ids.receiver_external_id
      (.receiver_resp call_id (F_OT sender choice))
  }
  label_matches := rfl
}

def receive_sender (ids : OTIds) (st : State)
    (call_id : Nat) (sender : OTSenderInput) : State :=
  if lookup_sender st.sender_reqs call_id |>.isSome then
    st
  else
    let sender_reqs := insert_sender_if_absent st.sender_reqs call_id sender
    match lookup_receiver st.receiver_reqs call_id with
    | some choice =>
        { sender_reqs := remove_sender sender_reqs call_id
          receiver_reqs := remove_receiver st.receiver_reqs call_id
          pending_outgoing := some (build_receiver_response ids call_id sender choice) }
    | none =>
        { st with sender_reqs := sender_reqs }

def receive_receiver (ids : OTIds) (st : State)
    (call_id : Nat) (choice : OTReceiverInput) : State :=
  if lookup_receiver st.receiver_reqs call_id |>.isSome then
    st
  else
    let receiver_reqs := insert_receiver_if_absent st.receiver_reqs call_id choice
    match lookup_sender st.sender_reqs call_id with
    | some sender =>
        { sender_reqs := remove_sender st.sender_reqs call_id
          receiver_reqs := remove_receiver receiver_reqs call_id
          pending_outgoing := some (build_receiver_response ids call_id sender choice) }
    | none =>
        { st with receiver_reqs := receiver_reqs }

def receive (ids : OTIds) (st : State) (msg : Message OTPayload) : State :=
  match msg.source, msg.label, msg.payload with
  | some src, .input, .to_functionality _ (.sender_req call_id sender) =>
      if _h_src : src = ids.sender_id then
        receive_sender ids st call_id sender
      else
        st
  | some src, .input, .to_functionality _ (.receiver_req call_id choice) =>
      if _h_src : src = ids.receiver_id then
        receive_receiver ids st call_id choice
      else
        st
  | _, _, _ => st

noncomputable def resume (st : State) : PMF (ActivationResult OTPayload State) :=
  match st.pending_outgoing with
  | none =>
      PMF.pure { state := st, outgoing? := none }
  | some envelope =>
      PMF.pure {
        state := { st with pending_outgoing := none }
        outgoing? := some envelope
      }

def communication_set (ids : OTIds) : Finset CommPort :=
  { sender_port ids, receiver_port ids }

noncomputable def machine (ids : OTIds) : Machine OTPayload Unit where
  id := ids.functionality_id
  communication_set := communication_set ids
  program := {
    LocalState := State
    init := init_state
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
      rcases hp with rfl | rfl
      · rfl
      · rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [communication_set] at hp₁ hp₂
      rcases hp₁ with rfl | rfl <;> rcases hp₂ with rfl | rfl
      · rfl
      · exact (ids.sender_ne_receiver h_dest).elim
      · exact (ids.sender_ne_receiver h_dest.symm).elim
      · rfl

end OTImpl

private def ot_party_external_ids (ids : OTIds) (pid : MachineId) : Finset MachineId :=
  if pid = ids.sender_id then
    {ids.sender_external_id}
  else if pid = ids.receiver_id then
    {ids.receiver_external_id}
  else
    ∅

@[simp] private theorem ot_party_external_ids_sender (ids : OTIds) :
    ot_party_external_ids ids ids.sender_id = {ids.sender_external_id} := by
  simp [ot_party_external_ids]

@[simp] private theorem ot_party_external_ids_receiver (ids : OTIds) :
    ot_party_external_ids ids ids.receiver_id = {ids.receiver_external_id} := by
  simp [ot_party_external_ids, ids.sender_ne_receiver, ids.sender_ne_receiver.symm]

/--
OT 的理想功能机与其通信包装由 `IdealOT` 统一给出。

这里先固定 OT 的业务消息体、payload 包装类型和参与方/功能机的 identities；
具体的 ideal functionality 机器封装在 `IdealOT` 这个构造器里。
-/
noncomputable def IdealOT : OTIds → IdealFunctionality OTPayload
  | ids => {
      party_ids := [ids.sender_id, ids.receiver_id]
      functionality_id := ids.functionality_id
      machine := OTImpl.machine ids
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
      party_external_ids := ot_party_external_ids ids
      external_ids_nonempty := by
        intro pid h_pid
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simpa using (show ({ids.sender_external_id} : Finset MachineId).Nonempty from by simp)
        · simpa using (show ({ids.receiver_external_id} : Finset MachineId).Nonempty from by simp)
      external_ids_outside_parties := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [ot_party_external_ids] at h_ext
          rcases h_ext with rfl
          simp [ids.sender_external_separated.1, ids.sender_external_separated.2.1]
        · simp [ot_party_external_ids, ids.sender_ne_receiver, ids.sender_ne_receiver.symm] at h_ext
          rcases h_ext with rfl
          simp [ids.receiver_external_separated.1, ids.receiver_external_separated.2.1]
      external_ids_separated := by
        intro pid h_pid ext h_ext
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · simp [ot_party_external_ids] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.sender_external_separated.2.2.1,
            ids.sender_external_separated.2.2.2.1,
            ids.sender_external_separated.2.2.2.2⟩
        · simp [ot_party_external_ids, ids.sender_ne_receiver, ids.sender_ne_receiver.symm] at h_ext
          rcases h_ext with rfl
          exact ⟨ids.receiver_external_separated.2.2.1,
            ids.receiver_external_separated.2.2.2.1,
            ids.receiver_external_separated.2.2.2.2⟩
      dummy_local_state := Option (Message OTPayload)
      dummy_init := none
      dummy_receive := fun _ msg => some msg
      dummy_pending := fun st => st
      dummy_clear := fun _ => none
      wrap_input := fun caller_source payload =>
        match payload with
        | .plain body => .to_functionality caller_source body
        | other => other
      unwrap_output := fun payload =>
        match payload with
        | .from_functionality dest body => some (dest, .plain body)
        | _ => none
      functionality_ports_to_parties := by
        intro pid h_pid
        have h_cases : pid = ids.sender_id ∨ pid = ids.receiver_id := by
          simpa using h_pid
        rcases h_cases with rfl | rfl
        · refine ⟨sender_port ids, ?_, rfl, rfl⟩
          change sender_port ids ∈ ({sender_port ids, receiver_port ids} : Finset CommPort)
          simp [ids.sender_ne_receiver]
        · refine ⟨receiver_port ids, ?_, rfl, rfl⟩
          change receiver_port ids ∈ ({sender_port ids, receiver_port ids} : Finset CommPort)
          simp [ids.sender_ne_receiver]
      functionality_comm_constraints := by
        intro p hp
        have hp' : p = sender_port ids ∨ p = receiver_port ids := by
          change p ∈ ({sender_port ids, receiver_port ids} : Finset CommPort) at hp
          simpa [ids.sender_ne_receiver] using hp
        rcases hp' with rfl | rfl
        · refine ⟨?_, rfl⟩
          change ids.sender_id ∈ ([ids.sender_id, ids.receiver_id] : List MachineId).toFinset
          simp
        · refine ⟨?_, rfl⟩
          change ids.receiver_id ∈ ([ids.sender_id, ids.receiver_id] : List MachineId).toFinset
          simp
    }

end LeanCryptoProtocols.UC.Functionality

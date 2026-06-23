import LeanCryptoProtocols.UC.Controller

/-!
# 理想功能 / dummy party / ideal protocol

本文件建立在 `Machine.lean` 与 `Controller.lean` 之上，给出：

- 理想功能；
- dummy party；
- 从理想功能自动生成 ideal protocol 的构造接口。

这里固定采用 uniform 的 restricted model：
不显式建模额外辅助输入，只保留安全参数 `n`。
-/

universe u

namespace LeanCryptoProtocols.UC

/--
理想功能对象。

按 Canetti 原文，理想功能本身只是一个 machine；
但为了能自动构造 dummy parties，
这里额外记录：

- 参与方 identities；
- 每个参与方对应的 external identities；
- 如何把环境输入包装成送给功能机的 payload；
- 如何把功能机返回的 payload 解析成目标 identity 与外发 payload。
-/
structure IdealFunctionality (Payload : Type u) where
  party_ids : List MachineId
  functionality_id : MachineId
  machine : Machine Payload Unit
  id_matches : machine.id = functionality_id
  party_ids_nodup : party_ids.Nodup
  parties_separated : env_id ∉ party_ids ∧ adv_id ∉ party_ids
  functionality_separated : functionality_id ≠ env_id ∧ functionality_id ≠ adv_id
  functionality_not_party : functionality_id ∉ party_ids
  party_external_ids : MachineId → Finset MachineId
  external_ids_nonempty :
    ∀ pid ∈ party_ids, (party_external_ids pid).Nonempty
  external_ids_outside_parties :
    ∀ pid ∈ party_ids, ∀ ext ∈ party_external_ids pid, ext ∉ party_ids
  external_ids_separated :
    ∀ pid ∈ party_ids, ∀ ext ∈ party_external_ids pid,
      ext ≠ functionality_id ∧ ext ≠ env_id ∧ ext ≠ adv_id
  dummy_local_state : Type
  dummy_init : ℕ → dummy_local_state
  dummy_receive : dummy_local_state → Message Payload → dummy_local_state
  dummy_pending : dummy_local_state → Option (Message Payload)
  dummy_clear : dummy_local_state → dummy_local_state
  wrap_input : Option MachineId → Payload → Payload
  unwrap_output : Payload → Option (MachineId × Payload)
  functionality_ports_to_parties :
    ∀ pid ∈ party_ids,
      ∃ p ∈ machine.communication_set, p.dest = pid ∧ p.label = .subroutineOutput
  functionality_comm_constraints :
    ∀ p ∈ machine.communication_set,
      (p.dest ∈ party_ids.toFinset ∧ p.label = .subroutineOutput) ∨
        (p.dest = adv_id ∧ p.label = .backdoor)

/--
dummy party。

这是 `mk_dummy_party` 的审计输出对象，而不是协议设计者需要手写的主入口。
-/
structure DummyParty (Payload : Type u) where
  party_id : MachineId
  functionality_id : MachineId
  external_ids : Finset MachineId
  machine : Machine Payload Unit
  id_matches : machine.id = party_id
  no_backdoor :
    ∀ p ∈ machine.communication_set, p.label = .backdoor → False
  input_port_present :
    ∃ p ∈ machine.communication_set, p.dest = functionality_id ∧ p.label = .input
  external_ports_complete :
    ∀ ext ∈ external_ids,
      ∃ p ∈ machine.communication_set, p.dest = ext ∧ p.label = .subroutineOutput
  communication_constraints :
    ∀ p ∈ machine.communication_set,
      (p.dest = functionality_id ∧ p.label = .input) ∨
        (p.dest ∈ external_ids ∧ p.label = .subroutineOutput)

/-- 把 dummy party 打包成异质 machine。 -/
def DummyParty.to_any_machine {Payload : Type u} (d : DummyParty Payload) : AnyMachine Payload :=
  ⟨Unit, d.machine⟩

namespace DummyPartyImpl

private theorem party_ne_functionality {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id : MachineId} (h_party : party_id ∈ f.party_ids) :
    party_id ≠ f.functionality_id := by
  intro h_eq
  apply f.functionality_not_party
  simpa [h_eq] using h_party

private theorem party_ne_env {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id : MachineId} (h_party : party_id ∈ f.party_ids) :
    party_id ≠ env_id := by
  intro h_eq
  apply f.parties_separated.1
  simpa [h_eq] using h_party

private theorem party_ne_adv {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id : MachineId} (h_party : party_id ∈ f.party_ids) :
    party_id ≠ adv_id := by
  intro h_eq
  apply f.parties_separated.2
  simpa [h_eq] using h_party

private theorem external_ne_functionality {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id ext : MachineId}
    (h_party : party_id ∈ f.party_ids)
    (h_ext : ext ∈ f.party_external_ids party_id) :
    ext ≠ f.functionality_id :=
  (f.external_ids_separated party_id h_party ext h_ext).1

private theorem external_ne_env {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id ext : MachineId}
    (h_party : party_id ∈ f.party_ids)
    (h_ext : ext ∈ f.party_external_ids party_id) :
    ext ≠ env_id :=
  (f.external_ids_separated party_id h_party ext h_ext).2.1

private theorem external_ne_adv {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id ext : MachineId}
    (h_party : party_id ∈ f.party_ids)
    (h_ext : ext ∈ f.party_external_ids party_id) :
    ext ≠ adv_id :=
  (f.external_ids_separated party_id h_party ext h_ext).2.2

private theorem external_ne_party {Payload : Type u} (f : IdealFunctionality Payload)
    {party_id ext : MachineId}
    (h_party : party_id ∈ f.party_ids)
    (h_ext : ext ∈ f.party_external_ids party_id) :
    ext ≠ party_id := by
  intro h_eq
  have h_not_mem := f.external_ids_outside_parties party_id h_party ext h_ext
  apply h_not_mem
  simpa [h_eq] using h_party

noncomputable def input_port {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) : CommPort :=
  mk_input_port
    party_id
    f.functionality_id
    (party_ne_functionality f h_party)
    (party_ne_adv f h_party)
    f.functionality_separated.2

@[simp] theorem input_port_dest {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) :
    (input_port f party_id h_party).dest = f.functionality_id := rfl

@[simp] theorem input_port_label {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) :
    (input_port f party_id h_party).label = .input := rfl

@[simp] theorem input_port_owner {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) :
    (input_port f party_id h_party).owner = party_id := rfl

noncomputable def output_port_of_member {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids)
    (ext : { x // x ∈ f.party_external_ids party_id }) : CommPort :=
  mk_subroutine_output_port
    party_id
    ext.1
    (external_ne_party f h_party ext.2).symm
    (party_ne_adv f h_party)
    (external_ne_adv f h_party ext.2)

@[simp] theorem output_port_dest {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids)
    (ext : { x // x ∈ f.party_external_ids party_id }) :
    (output_port_of_member f party_id h_party ext).dest = ext.1 := rfl

@[simp] theorem output_port_label {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids)
    (ext : { x // x ∈ f.party_external_ids party_id }) :
    (output_port_of_member f party_id h_party ext).label = .subroutineOutput := rfl

@[simp] theorem output_port_owner {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids)
    (ext : { x // x ∈ f.party_external_ids party_id }) :
    (output_port_of_member f party_id h_party ext).owner = party_id := rfl

noncomputable def output_ports {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) : Finset CommPort :=
  (f.party_external_ids party_id).attach.image
    (output_port_of_member f party_id h_party)

theorem mem_output_ports_of_member {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids)
    (ext : MachineId) (h_ext : ext ∈ f.party_external_ids party_id) :
    output_port_of_member f party_id h_party ⟨ext, h_ext⟩ ∈
      output_ports f party_id h_party := by
  classical
  refine Finset.mem_image.mpr ?_
  exact ⟨⟨ext, h_ext⟩, by simp, rfl⟩

noncomputable def output_port {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids)
    (dest : MachineId) : Option CommPort :=
  by
  classical
  if h_dest : dest ∈ f.party_external_ids party_id then
    exact some (output_port_of_member f party_id h_party ⟨dest, h_dest⟩)
  else
    exact none

/-- 构造 Dummy party 的 communication_set。 -/
noncomputable def communication_set {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) : Finset CommPort :=
  insert (input_port f party_id h_party) (output_ports f party_id h_party)

noncomputable def program {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) :
    MachineProgram Payload Unit where
  LocalState := f.dummy_local_state
  init := f.dummy_init
  receive := fun st msg => f.dummy_receive st msg
  resume st :=
    let cleared := f.dummy_clear st
    match f.dummy_pending st with
    | none =>
        PMF.pure {
          state := cleared
          outgoing? := none
        }
    | some msg =>
        match msg.label with
        | .input =>
            let out_msg : Message Payload := {
              source := some party_id
              label := .input
              payload := f.wrap_input msg.source msg.payload
            }
            PMF.pure {
              state := cleared
              outgoing? := some {
                port := input_port f party_id h_party
                message := out_msg
                label_matches := rfl
              }
            }
        | .subroutineOutput =>
            match f.unwrap_output msg.payload with
            | none =>
                PMF.pure {
                  state := cleared
                  outgoing? := none
                }
            | some (dest_id, payload') =>
                match h_lookup : output_port f party_id h_party dest_id with
                | none =>
                    PMF.pure {
                      state := cleared
                      outgoing? := none
                    }
                | some port =>
                    let out_msg : Message Payload := {
                      source := some party_id
                      label := .subroutineOutput
                      payload := payload'
                    }
                    PMF.pure {
                      state := cleared
                      outgoing? := some {
                        port := port
                        message := out_msg
                        label_matches := by
                          have h_port_label : port.label = .subroutineOutput := by
                            unfold output_port at h_lookup
                            classical
                            split at h_lookup
                            · injection h_lookup with h_eq
                              subst h_eq
                              rfl
                            · cases h_lookup
                          simpa [out_msg] using h_port_label
                      }
                    }
        | .backdoor =>
            PMF.pure {
              state := cleared
              outgoing? := none
            }
  is_halted := fun _ => false
  output := fun _ => ()

noncomputable def machine {Payload : Type u} (f : IdealFunctionality Payload)
    (party_id : MachineId) (h_party : party_id ∈ f.party_ids) :
    Machine Payload Unit where
  id := party_id
  communication_set := communication_set f party_id h_party
  program := program f party_id h_party
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with hp | hp
      · subst hp
        exact input_port_owner f party_id h_party
      · rcases Finset.mem_image.mp hp with ⟨ext, _, rfl⟩
        exact output_port_owner f party_id h_party ext
    · intro p₁ hp₁ p₂ hp₂ h_dest
      rcases Finset.mem_insert.mp hp₁ with hp₁ | hp₁
      · rcases Finset.mem_insert.mp hp₂ with hp₂ | hp₂
        · subst hp₁; subst hp₂; rfl
        · subst hp₁
          rcases Finset.mem_image.mp hp₂ with ⟨ext₂, _, rfl⟩
          have : False := external_ne_functionality f h_party ext₂.2 (by simpa using h_dest.symm)
          exact this.elim
      · rcases Finset.mem_insert.mp hp₂ with hp₂ | hp₂
        · subst hp₂
          rcases Finset.mem_image.mp hp₁ with ⟨ext₁, _, rfl⟩
          have : False := external_ne_functionality f h_party ext₁.2 (by simpa using h_dest)
          exact this.elim
        · rcases Finset.mem_image.mp hp₁ with ⟨ext₁, _, rfl⟩
          rcases Finset.mem_image.mp hp₂ with ⟨ext₂, _, rfl⟩
          have h_val : ext₁.1 = ext₂.1 := by simpa using h_dest
          have h_sub : ext₁ = ext₂ := Subtype.ext h_val
          cases h_sub
          rfl

end DummyPartyImpl

/-- 从理想功能自动生成一个 dummy party。 -/
noncomputable def mk_dummy_party {Payload : Type u}
    (f : IdealFunctionality Payload) (party_id : MachineId)
    (h_party : party_id ∈ f.party_ids) : DummyParty Payload where
  party_id := party_id
  functionality_id := f.functionality_id
  external_ids := f.party_external_ids party_id
  machine := DummyPartyImpl.machine f party_id h_party
  id_matches := rfl
  no_backdoor := by
    classical
    intro p hp h_backdoor
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst hp
      cases h_backdoor
    · rcases Finset.mem_image.mp hp with ⟨ext, _, rfl⟩
      cases h_backdoor
  input_port_present := by
    refine ⟨DummyPartyImpl.input_port f party_id h_party, ?_, rfl, rfl⟩
    exact Finset.mem_insert_self _ _
  external_ports_complete := by
    intro ext h_ext
    refine
      ⟨DummyPartyImpl.output_port_of_member f party_id h_party ⟨ext, h_ext⟩,
        ?_, rfl, rfl⟩
    exact Finset.mem_insert_of_mem
      (DummyPartyImpl.mem_output_ports_of_member f party_id h_party ext h_ext)
  communication_constraints := by
    classical
    intro p hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst hp
      exact Or.inl ⟨rfl, rfl⟩
    · rcases Finset.mem_image.mp hp with ⟨ext, _, rfl⟩
      exact Or.inr ⟨ext.2, rfl⟩

private noncomputable def mk_dummy_parties_aux {Payload : Type u} (f : IdealFunctionality Payload) :
    (l : List MachineId) →
    (∀ pid, pid ∈ l → pid ∈ f.party_ids) →
    List (DummyParty Payload)
  | [], _ => []
  | pid :: rest, h =>
      mk_dummy_party f pid (h pid (by simp)) ::
        mk_dummy_parties_aux f rest (fun x hx => h x (by simp [hx]))

private theorem mk_dummy_parties_aux_map_party_id {Payload : Type u}
    (f : IdealFunctionality Payload) :
    ∀ l h,
      (mk_dummy_parties_aux f l h).map DummyParty.party_id = l
  | [], _ => by rfl
  | pid :: rest, h => by
      simp [mk_dummy_parties_aux, mk_dummy_parties_aux_map_party_id, mk_dummy_party]

/-- 从理想功能的参与方列表自动生成所有 dummy parties。 -/
noncomputable def mk_dummy_parties {Payload : Type u}
    (f : IdealFunctionality Payload) : List (DummyParty Payload) :=
  mk_dummy_parties_aux f f.party_ids (fun _ h => h)

private theorem mk_dummy_parties_map_party_id {Payload : Type u}
    (f : IdealFunctionality Payload) :
    (mk_dummy_parties f).map DummyParty.party_id = f.party_ids := by
  simpa [mk_dummy_parties] using
    mk_dummy_parties_aux_map_party_id f f.party_ids (fun pid h => h)

/-- `mk_dummy_parties` 生成的 dummy party ids 恰好等于 `party_ids`。 -/
theorem mk_dummy_parties_party_ids {Payload : Type u}
    (f : IdealFunctionality Payload) :
    (mk_dummy_parties f).map DummyParty.party_id = f.party_ids :=
  mk_dummy_parties_map_party_id f

private theorem mk_dummy_parties_mem_party_data {Payload : Type u}
    (f : IdealFunctionality Payload) {d : DummyParty Payload}
    (h_mem : d ∈ mk_dummy_parties f) :
    d.party_id ∈ f.party_ids ∧
      d.functionality_id = f.functionality_id ∧
      d.external_ids = f.party_external_ids d.party_id := by
  unfold mk_dummy_parties at h_mem
  have h_aux :
      ∀ l h {d : DummyParty Payload},
        d ∈ mk_dummy_parties_aux f l h →
          d.party_id ∈ l ∧
            d.functionality_id = f.functionality_id ∧
            d.external_ids = f.party_external_ids d.party_id := by
    intro l
    induction l with
    | nil =>
        intro h d h_mem
        cases h_mem
    | cons pid rest ih =>
        intro h d h_mem
        simp only [mk_dummy_parties_aux, List.mem_cons] at h_mem
        rcases h_mem with rfl | h_tail
        · refine ⟨?_, rfl, rfl⟩
          simp [mk_dummy_party]
        · rcases ih (fun x hx => h x (by simp [hx])) h_tail with ⟨h_mem_rest, h_func, h_exts⟩
          exact ⟨by simp [h_mem_rest], h_func, h_exts⟩
  simpa using h_aux f.party_ids (fun pid h => h) h_mem

private theorem exists_dummy_party_for_id {Payload : Type u}
    (f : IdealFunctionality Payload) {pid : MachineId}
    (h_pid : pid ∈ f.party_ids) :
    ∃ d ∈ mk_dummy_parties f, d.party_id = pid := by
  have h_mem_map : pid ∈ (mk_dummy_parties f).map DummyParty.party_id := by
    simpa [mk_dummy_parties_map_party_id f] using h_pid
  rcases List.mem_map.mp h_mem_map with ⟨d, hd, hdid⟩
  exact ⟨d, hd, hdid⟩

@[simp] private theorem dummy_to_any_machine_id {Payload : Type u}
    (d : DummyParty Payload) :
    AnyMachine.id d.to_any_machine = d.party_id := by
  simp [DummyParty.to_any_machine, AnyMachine.id, d.id_matches]

/--
ideal protocol。

它由若干 dummy parties 与一个理想功能机组成；这里显式暴露这三部分，
便于后续审计。
-/
structure IdealProtocol (Payload : Type u) where
  protocol : Protocol Payload
  functionality : IdealFunctionality Payload
  dummy_parties : List (DummyParty Payload)
  machines_eq :
    protocol.machines =
      dummy_parties.map DummyParty.to_any_machine ++ [⟨Unit, functionality.machine⟩]

/--
从理想功能自动生成 ideal protocol。

这里把 proof-heavy 的 protocol-shape 组装集中放在一个构造器里，供 `UCRealizesAt`
复用。
-/
noncomputable def mk_ideal_protocol {Payload : Type u}
    (f : IdealFunctionality Payload) : IdealProtocol Payload := by
  let dummies := mk_dummy_parties f
  let machines : List (AnyMachine Payload) :=
    dummies.map DummyParty.to_any_machine ++ [⟨Unit, f.machine⟩]
  have hdummy_ids :
      machine_ids (dummies.map DummyParty.to_any_machine) = dummies.map DummyParty.party_id := by
    induction dummies with
    | nil => rfl
    | cons d rest ih =>
        simp [machine_ids, dummy_to_any_machine_id]
  have h_party_ids :
      dummies.map DummyParty.party_id = f.party_ids :=
    mk_dummy_parties_map_party_id f
  have h_ids : machine_ids machines = f.party_ids ++ [f.functionality_id] := by
    calc
      machine_ids machines
          =
            machine_ids (dummies.map DummyParty.to_any_machine) ++
              [AnyMachine.id ⟨Unit, f.machine⟩] := by
              simp [machines, machine_ids]
      _ = dummies.map DummyParty.party_id ++ [f.functionality_id] := by
              simp [hdummy_ids, AnyMachine.id, f.id_matches]
      _ = f.party_ids ++ [f.functionality_id] := by
              rw [h_party_ids]
  let protocol : Protocol Payload := {
    machines := machines
    unique_ids := by
      rw [h_ids]
      simpa using f.party_ids_nodup.concat f.functionality_not_party
    caller_has_matching_subroutine := by
      intro m hm mid h_caller
      have hm_cases := List.mem_append.mp hm
      rcases hm_cases with h_dummy | h_fun
      · rcases List.mem_map.mp h_dummy with ⟨d, hd, rfl⟩
        rcases h_caller with ⟨p, hp, h_dest, h_label⟩
        have h_comm := d.communication_constraints p hp
        rcases h_comm with h_in | h_out
        · have h_data := mk_dummy_parties_mem_party_data f hd
          rcases h_data with ⟨h_party, h_func, _⟩
          refine ⟨⟨Unit, f.machine⟩, ?_, ?_, ?_⟩
          · exact List.mem_append.mpr <| Or.inr (by simp)
          · rw [show AnyMachine.id ⟨Unit, f.machine⟩ = f.functionality_id by
                  simp [AnyMachine.id, f.id_matches]]
            rw [← h_func, ← h_in.1, ← h_dest]
          · rcases f.functionality_ports_to_parties d.party_id h_party with
              ⟨p', hp', hpdest, hplabel⟩
            simpa [AnyMachine.id, DummyParty.to_any_machine, d.id_matches]
              using ⟨p', hp', hpdest, hplabel⟩
        · simp [h_out.2] at h_label
      · rcases List.mem_singleton.mp h_fun with rfl
        rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
        have h_comm := f.functionality_comm_constraints p hp
        rcases h_comm with h_party | h_adv
        · simp [h_party.2] at h_label
        · simp [h_adv.2] at h_label
    subroutine_has_matching_caller := by
      intro m hm mid h_sub h_mid_mem
      have hm_cases := List.mem_append.mp hm
      rcases hm_cases with h_dummy | h_fun
      · rcases List.mem_map.mp h_dummy with ⟨d, hd, rfl⟩
        rcases h_sub with ⟨p, hp, h_dest, h_label⟩
        have h_comm := d.communication_constraints p hp
        rcases h_comm with h_in | h_out
        · simp [h_in.2] at h_label
        · have h_data := mk_dummy_parties_mem_party_data f hd
          rcases h_data with ⟨h_party, _h_func, h_exts⟩
          have h_mid_cases : mid ∈ f.party_ids ∨ mid = f.functionality_id := by
            rw [h_ids] at h_mid_mem
            simp only [List.mem_append, List.mem_singleton] at h_mid_mem
            exact h_mid_mem
          rcases h_mid_cases with h_mid_party | h_mid_fun
          · have h_not_mem := f.external_ids_outside_parties d.party_id h_party mid
                (by simpa [h_dest, h_exts] using h_out.1)
            exact (h_not_mem h_mid_party).elim
          · have h_sep := f.external_ids_separated d.party_id h_party mid
                (by simpa [h_dest, h_exts] using h_out.1)
            exact (h_sep.1 h_mid_fun).elim
      · rcases List.mem_singleton.mp h_fun with rfl
        rcases h_sub with ⟨p, hp, h_dest, _h_label⟩
        have h_comm := f.functionality_comm_constraints p hp
        have h_mid_party : mid ∈ f.party_ids := by
          rcases h_comm with h_party | h_adv
          · simpa [h_dest] using h_party.1
          · have h_mid_adv : mid = adv_id := by
              simpa [h_dest] using h_adv.1
            have : adv_id ∈ f.party_ids ++ [f.functionality_id] := by
              simpa [h_ids, h_mid_adv] using h_mid_mem
            have : False := by
              rcases List.mem_append.mp this with h_adv_party | h_adv_fun
              · exact f.parties_separated.2 h_adv_party
              · have h_eq : adv_id = f.functionality_id := by
                  simpa using h_adv_fun
                exact f.functionality_separated.2 h_eq.symm
            exact this.elim
        rcases exists_dummy_party_for_id f h_mid_party with ⟨d, hd, hd_id⟩
        have h_data := mk_dummy_parties_mem_party_data f hd
        rcases h_data with ⟨_h_party, h_func, _h_exts⟩
        refine ⟨d.to_any_machine, ?_, ?_, ?_⟩
        · exact List.mem_append.mpr <| Or.inl (List.mem_map.mpr ⟨d, hd, rfl⟩)
        · simpa [dummy_to_any_machine_id] using hd_id
        · rcases d.input_port_present with ⟨p', hp', hpdest, hplabel⟩
          rw [h_func] at hpdest
          exact ⟨p', hp', by simpa [AnyMachine.id, f.id_matches] using hpdest, hplabel⟩
    env_separated := by
      intro h_env
      have : env_id ∈ f.party_ids ++ [f.functionality_id] := by
        simpa [h_ids] using h_env
      rcases List.mem_append.mp this with h_env | h_env
      · exact f.parties_separated.1 h_env
      · have h_eq : env_id = f.functionality_id := by simpa using h_env
        have h_eq' : f.functionality_id = env_id := h_eq.symm
        exact f.functionality_separated.1 h_eq'
    adv_separated := by
      intro h_adv
      have : adv_id ∈ f.party_ids ++ [f.functionality_id] := by
        simpa [h_ids] using h_adv
      rcases List.mem_append.mp this with h_adv | h_adv
      · exact f.parties_separated.2 h_adv
      · have h_eq : adv_id = f.functionality_id := by simpa using h_adv
        have h_eq' : f.functionality_id = adv_id := h_eq.symm
        exact f.functionality_separated.2 h_eq'
    no_direct_environment_communication := by
      intro m hm p hp
      have hm_cases := List.mem_append.mp hm
      rcases hm_cases with h_dummy | h_fun
      · rcases List.mem_map.mp h_dummy with ⟨d, hd, rfl⟩
        have h_data := mk_dummy_parties_mem_party_data f hd
        rcases h_data with ⟨h_party, h_func, h_exts⟩
        have h_comm := d.communication_constraints p hp
        rcases h_comm with h_in | h_out
        · rw [h_func] at h_in
          simpa [h_in.1] using f.functionality_separated.1
        · rw [h_exts] at h_out
          have h_sep := f.external_ids_separated d.party_id h_party p.dest h_out.1
          exact h_sep.2.1
      · rcases List.mem_singleton.mp h_fun with rfl
        have h_comm := f.functionality_comm_constraints p hp
        rcases h_comm with h_party | h_adv
        · intro h_eq
          exact f.parties_separated.1 (by simpa [h_eq] using h_party.1)
        · intro h_eq
          simp [h_adv.1, env_id, adv_id] at h_eq
    adversary_communication_is_backdoor := by
      intro m hm p hp h_dest
      have hm_cases := List.mem_append.mp hm
      rcases hm_cases with h_dummy | h_fun
      · rcases List.mem_map.mp h_dummy with ⟨d, hd, rfl⟩
        have h_data := mk_dummy_parties_mem_party_data f hd
        rcases h_data with ⟨h_party, h_func, h_exts⟩
        have h_comm := d.communication_constraints p hp
        rcases h_comm with h_in | h_out
        · rw [h_func] at h_in
          have : f.functionality_id ≠ adv_id := f.functionality_separated.2
          exact (this (by simpa [h_in.1] using h_dest)).elim
        · rw [h_exts] at h_out
          have h_sep := f.external_ids_separated d.party_id h_party p.dest h_out.1
          exact (h_sep.2.2 h_dest).elim
      · rcases List.mem_singleton.mp h_fun with rfl
        have h_comm := f.functionality_comm_constraints p hp
        rcases h_comm with h_party | h_adv
        · have : False := by
            have h_not_adv := f.parties_separated.2
            exact h_not_adv (by simpa [h_dest] using h_party.1)
          exact this.elim
        · simpa [h_adv.1] using h_adv.2
  }
  exact {
    protocol := protocol
    functionality := f
    dummy_parties := dummies
    machines_eq := rfl
  }

/-- `mk_ideal_protocol` 的 machine ids 恰好是 `party_ids ++ [functionality_id]`。 -/
theorem mk_ideal_protocol_machine_ids {Payload : Type u}
    (f : IdealFunctionality Payload) :
    machine_ids (mk_ideal_protocol f).protocol.machines =
      f.party_ids ++ [f.functionality_id] := by
  unfold mk_ideal_protocol
  let dummies := mk_dummy_parties f
  let machines : List (AnyMachine Payload) :=
    dummies.map DummyParty.to_any_machine ++ [⟨Unit, f.machine⟩]
  have hdummy_ids :
      machine_ids (dummies.map DummyParty.to_any_machine) =
        dummies.map DummyParty.party_id := by
    induction dummies with
    | nil => rfl
    | cons d rest ih =>
        simp [machine_ids, dummy_to_any_machine_id]
  have h_party_ids :
      dummies.map DummyParty.party_id = f.party_ids := by
    simp [dummies, mk_dummy_parties_party_ids]
  calc
    machine_ids machines
        =
          machine_ids (dummies.map DummyParty.to_any_machine) ++
            [AnyMachine.id ⟨Unit, f.machine⟩] := by
            simp [machines, machine_ids]
    _ = dummies.map DummyParty.party_id ++ [f.functionality_id] := by
            simp [hdummy_ids, AnyMachine.id, f.id_matches]
    _ = f.party_ids ++ [f.functionality_id] := by
            rw [h_party_ids]

/-- `mk_ideal_protocol` 中的 machine identities 正好是 dummy parties 与功能机。 -/
theorem mk_ideal_protocol_has_machine_id_iff {Payload : Type u}
    (f : IdealFunctionality Payload) (mid : MachineId) :
    (mk_ideal_protocol f).protocol.has_machine_id mid ↔
      mid ∈ f.party_ids ∨ mid = f.functionality_id := by
  classical
  simp [Protocol.has_machine_id, mk_ideal_protocol_machine_ids]

/-- 自动生成的 ideal protocol 中，dummy party identities 正好是 main machines。 -/
theorem mk_ideal_protocol_is_main_machine_iff {Payload : Type u}
    (f : IdealFunctionality Payload) (mid : MachineId) :
    (mk_ideal_protocol f).protocol.is_main_machine mid ↔
      mid ∈ f.party_ids := by
  classical
  constructor
  · intro h_main
    rcases h_main with ⟨m, hm, h_id, ext_id, h_ext⟩
    rcases h_ext with ⟨hm_ext, h_sub, h_external⟩
    have h_machines := (mk_ideal_protocol f).machines_eq
    rw [h_machines] at hm
    rcases List.mem_append.mp hm with h_dummy | h_functionality
    · rcases List.mem_map.mp h_dummy with ⟨d, hd, rfl⟩
      have h_data := mk_dummy_parties_mem_party_data f hd
      rcases h_data with ⟨h_party, _h_func, _h_exts⟩
      rw [← h_id]
      simpa [dummy_to_any_machine_id] using h_party
    · rcases List.mem_singleton.mp h_functionality with rfl
      rcases h_sub with ⟨p, hp, h_dest, h_label⟩
      have h_comm := f.functionality_comm_constraints p hp
      rcases h_comm with h_party | h_adv
      · have h_ext_mem : ext_id ∈ machine_ids (mk_ideal_protocol f).protocol.machines := by
          rw [mk_ideal_protocol_machine_ids]
          exact List.mem_append.mpr (Or.inl (by simpa [h_dest] using h_party.1))
        exact (h_external h_ext_mem).elim
      · simp [h_adv.2] at h_label
  · intro h_party
    rcases exists_dummy_party_for_id f h_party with ⟨d, hd, hd_id⟩
    have h_data := mk_dummy_parties_mem_party_data f hd
    rcases h_data with ⟨h_d_party, _h_func, h_exts⟩
    rcases f.external_ids_nonempty d.party_id (by simpa [hd_id] using h_party) with
      ⟨ext_id, h_ext_id⟩
    rcases d.external_ports_complete ext_id (by simpa [h_exts] using h_ext_id) with
      ⟨p, hp, h_dest, h_label⟩
    refine ⟨d.to_any_machine, ?_, ?_, ext_id, ?_⟩
    · rw [(mk_ideal_protocol f).machines_eq]
      exact List.mem_append.mpr <| Or.inl (List.mem_map.mpr ⟨d, hd, rfl⟩)
    · simpa [dummy_to_any_machine_id] using hd_id
    · refine ⟨?_, ⟨p, hp, h_dest, h_label⟩, ?_⟩
      · rw [(mk_ideal_protocol f).machines_eq]
        exact List.mem_append.mpr <| Or.inl (List.mem_map.mpr ⟨d, hd, rfl⟩)
      · intro h_ext_machine
        rw [mk_ideal_protocol_machine_ids] at h_ext_machine
        rcases List.mem_append.mp h_ext_machine with h_ext_party | h_ext_func
        · exact
            (f.external_ids_outside_parties d.party_id h_d_party ext_id
              (by simpa [h_exts] using h_ext_id)) h_ext_party
        · have h_ext_func_eq : ext_id = f.functionality_id := by
            simpa using h_ext_func
          exact
            ((f.external_ids_separated d.party_id h_d_party ext_id
              (by simpa [h_exts] using h_ext_id)).1 h_ext_func_eq)

/-- 自动生成的 ideal protocol 中，唯一 internal machine 是理想功能机。 -/
theorem mk_ideal_protocol_is_internal_machine_iff {Payload : Type u}
    (f : IdealFunctionality Payload) (mid : MachineId) :
    (mk_ideal_protocol f).protocol.is_internal_machine mid ↔
      mid = f.functionality_id := by
  classical
  constructor
  · intro h_internal
    rcases h_internal with ⟨h_has, h_not_main⟩
    rcases (mk_ideal_protocol_has_machine_id_iff f mid).1 h_has with
      h_party | h_func
    · exact (h_not_main
        ((mk_ideal_protocol_is_main_machine_iff f mid).2 h_party)).elim
    · exact h_func
  · intro h_eq
    refine ⟨?_, ?_⟩
    · exact (mk_ideal_protocol_has_machine_id_iff f mid).2 (Or.inr h_eq)
    · intro h_main
      have h_party :=
        (mk_ideal_protocol_is_main_machine_iff f mid).1 h_main
      rw [h_eq] at h_party
      exact f.functionality_not_party h_party

end LeanCryptoProtocols.UC

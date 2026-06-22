import LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE.Certificate.CertificateObjects

/-!
# DHKE 子证明的 protocol well-formed 证明
-/

set_option linter.flexible false
set_option linter.style.nativeDecide false

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Assumptions
open LeanCryptoProtocols.CaseStudy.SMCEasyUC

noncomputable def ke_sender_machine
    (gen : GroupGenerator) : Machine SMCEasyUCPayload Unit where
  id := ke_sender_id
  communication_set :=
    { ke_sender_to_smc_sender_port
    , ke_sender_to_forw_ke_forward_port
    , ke_sender_to_forw_ke_return_port
    }
  program := initiator_program gen
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [ke_sender_to_smc_sender_port, ke_sender_to_forw_ke_forward_port,
        ke_sender_to_forw_ke_return_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [ke_sender_to_smc_sender_port, ke_sender_to_forw_ke_forward_port,
        ke_sender_to_forw_ke_return_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (smc_sender_ne_forw_ke_forward
          (by
            simpa [ke_sender_to_smc_sender_port,
              ke_sender_to_forw_ke_forward_port] using h_dest)).elim
      · exact (smc_sender_ne_forw_ke_return
          (by
            simpa [ke_sender_to_smc_sender_port,
              ke_sender_to_forw_ke_return_port] using h_dest)).elim
      · exact (smc_sender_ne_forw_ke_forward
          (by
            simpa [ke_sender_to_smc_sender_port,
              ke_sender_to_forw_ke_forward_port] using h_dest.symm)).elim
      · rfl
      · exact (forw_ke_forward_ne_forw_ke_return
          (by
            simpa [ke_sender_to_forw_ke_forward_port,
              ke_sender_to_forw_ke_return_port] using h_dest)).elim
      · exact (smc_sender_ne_forw_ke_return
          (by
            simpa [ke_sender_to_smc_sender_port,
              ke_sender_to_forw_ke_return_port] using h_dest.symm)).elim
      · exact (forw_ke_forward_ne_forw_ke_return
          (by
            simpa [ke_sender_to_forw_ke_forward_port,
              ke_sender_to_forw_ke_return_port] using h_dest.symm)).elim
      · rfl

noncomputable def ke_receiver_machine
    (gen : GroupGenerator) : Machine SMCEasyUCPayload Unit where
  id := ke_receiver_id
  communication_set :=
    { ke_receiver_to_smc_receiver_port
    , ke_receiver_to_forw_ke_forward_port
    , ke_receiver_to_forw_ke_return_port
    }
  program := responder_program gen
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [ke_receiver_to_smc_receiver_port, ke_receiver_to_forw_ke_forward_port,
        ke_receiver_to_forw_ke_return_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [ke_receiver_to_smc_receiver_port, ke_receiver_to_forw_ke_forward_port,
        ke_receiver_to_forw_ke_return_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (smc_receiver_ne_forw_ke_forward
          (by
            simpa [ke_receiver_to_smc_receiver_port,
              ke_receiver_to_forw_ke_forward_port] using h_dest)).elim
      · exact (smc_receiver_ne_forw_ke_return
          (by
            simpa [ke_receiver_to_smc_receiver_port,
              ke_receiver_to_forw_ke_return_port] using h_dest)).elim
      · exact (smc_receiver_ne_forw_ke_forward
          (by
            simpa [ke_receiver_to_smc_receiver_port,
              ke_receiver_to_forw_ke_forward_port] using h_dest.symm)).elim
      · rfl
      · exact (forw_ke_forward_ne_forw_ke_return
          (by
            simpa [ke_receiver_to_forw_ke_forward_port,
              ke_receiver_to_forw_ke_return_port] using h_dest)).elim
      · exact (smc_receiver_ne_forw_ke_return
          (by
            simpa [ke_receiver_to_smc_receiver_port,
              ke_receiver_to_forw_ke_return_port] using h_dest.symm)).elim
      · exact (forw_ke_forward_ne_forw_ke_return
          (by
            simpa [ke_receiver_to_forw_ke_forward_port,
              ke_receiver_to_forw_ke_return_port] using h_dest.symm)).elim
      · rfl

private theorem forw_has_subroutine_to_sender
    (ids : ForwIds) :
    is_subroutine_of_id (IdealForw ids).machine ids.sender_id := by
  refine ⟨forw_sender_port ids, ?_, rfl, rfl⟩
  change forw_sender_port ids ∈ Functionality.ForwImpl.communication_set ids
  simp [Functionality.ForwImpl.communication_set]

private theorem forw_has_subroutine_to_receiver
    (ids : ForwIds) :
    is_subroutine_of_id (IdealForw ids).machine ids.receiver_id := by
  refine ⟨forw_receiver_port ids, ?_, rfl, rfl⟩
  change forw_receiver_port ids ∈ Functionality.ForwImpl.communication_set ids
  simp [Functionality.ForwImpl.communication_set]

noncomputable def lift_machine_to_type1
    {Payload : Type} {Out : Type}
    (m : Machine.{0, 0, 0} Payload Out) :
    Machine.{0, 0, 1} Payload Out where
  id := m.id
  communication_set := m.communication_set
  program := {
    LocalState := ULift m.program.LocalState
    init := fun n => ⟨m.program.init n⟩
    receive := fun st msg =>
      ⟨m.program.receive st.down msg⟩
    resume := fun st =>
      PMF.map
        (fun r => {
          state := ⟨r.state⟩
          outgoing? := r.outgoing?
        })
        (m.program.resume st.down)
    is_halted := fun st => m.program.is_halted st.down
    output := fun st => m.program.output st.down
  }
  well_formed := m.well_formed

noncomputable def protocol_ke_receiver_machine
    (gen : GroupGenerator) : Machine.{0, 0, 1} SMCEasyUCPayload Unit :=
  ke_receiver_machine gen

noncomputable def forw_ke_forward_machine :
    Machine.{0, 0, 1} SMCEasyUCPayload Unit :=
  lift_machine_to_type1 (IdealForw forw_ke_forward_ids).machine

noncomputable def forw_ke_return_machine :
    Machine.{0, 0, 1} SMCEasyUCPayload Unit :=
  lift_machine_to_type1 (IdealForw forw_ke_return_ids).machine

private theorem lifted_forw_has_subroutine_to_sender
    (ids : ForwIds) :
    is_subroutine_of_id
      (lift_machine_to_type1 (IdealForw ids).machine)
      ids.sender_id := by
  simpa [lift_machine_to_type1] using forw_has_subroutine_to_sender ids

private theorem lifted_forw_has_subroutine_to_receiver
    (ids : ForwIds) :
    is_subroutine_of_id
      (lift_machine_to_type1 (IdealForw ids).machine)
      ids.receiver_id := by
  simpa [lift_machine_to_type1] using forw_has_subroutine_to_receiver ids

/-! ## Real DHKE protocol -/

/--
由 DDH-real witness 给出的真实 DHKE protocol 初始状态列表。

这个定义把公共群描述和两个 exponent 写入两台真实 KE party 的局部状态；
后续的 controller trace 证明会以同一个 witness 为耦合点。
-/
noncomputable def real_protocol_states_of_witness
    (gen : GroupGenerator) (n : ℕ) (witness : DDHRealWitness) :
    List (AnyMachineState SMCEasyUCPayload) :=
  [ ⟨⟨Unit, ke_sender_machine gen⟩,
      { (initiator_init n) with
        group? := some witness.G
        secret? := some witness.initiator_secret }⟩
  , ⟨⟨Unit, protocol_ke_receiver_machine gen⟩,
      { (responder_init n) with
        group? := some witness.G
        secret? := some witness.responder_secret }⟩
  , ⟨⟨Unit, forw_ke_forward_machine⟩,
      forw_ke_forward_machine.program.init n⟩
  , ⟨⟨Unit, forw_ke_return_machine⟩,
      forw_ke_return_machine.program.init n⟩
  ]

noncomputable def real_machines
    (gen : GroupGenerator) : List (AnyMachine SMCEasyUCPayload) :=
  [ ⟨Unit, ke_sender_machine gen⟩
  , ⟨Unit, protocol_ke_receiver_machine gen⟩
  , ⟨Unit, forw_ke_forward_machine⟩
  , ⟨Unit, forw_ke_return_machine⟩
  ]

/--
真实 DHKE protocol 的公共初始化。

controller 在安全参数 `n` 下先采样一次公共群描述 `G ← gen n`，再把同一个
`G` 写入两台 KE party 的初始状态。两台 party 后续只在该公共群中各自采样
secret exponent；这正是把真实执行嵌入 DDH-real sample 所需的公共 setup。
-/
noncomputable def real_initial_states
    (gen : GroupGenerator) (n : ℕ) :
    PMF (List (AnyMachineState SMCEasyUCPayload)) :=
  (ddh_real_witness gen n).bind fun witness =>
    PMF.pure (real_protocol_states_of_witness gen n witness)

/-- `real_initial_states` 正是对 witness 初始化列表的采样。 -/
theorem real_initial_states_eq_witness_bind
    (gen : GroupGenerator) (n : ℕ) :
    real_initial_states gen n =
      (ddh_real_witness gen n).bind fun witness =>
        PMF.pure (real_protocol_states_of_witness gen n witness) := by
  rfl

theorem machine_ids_real_machines
    (gen : GroupGenerator) :
    machine_ids (real_machines gen) = machine_id_list := by
  simp [machine_ids, real_machines, machine_id_list, AnyMachine.id,
    ke_sender_machine, protocol_ke_receiver_machine, ke_receiver_machine,
    forw_ke_forward_machine, forw_ke_return_machine, lift_machine_to_type1,
    IdealForw, Functionality.ForwImpl.machine, forw_ke_forward_ids,
    forw_ke_return_ids]

theorem real_unique_ids
    (gen : GroupGenerator) :
    (machine_ids (real_machines gen)).Nodup := by
  rw [machine_ids_real_machines gen]
  native_decide

theorem real_caller_has_matching_subroutine
    (gen : GroupGenerator) :
  ∀ m ∈ real_machines gen, ∀ mid : MachineId,
    is_caller_of_id m.2 mid →
      ∃ m' ∈ real_machines gen,
        AnyMachine.id m' = mid ∧ is_subroutine_of_id m'.2 (AnyMachine.id m) := by
  intro m hm mid h_caller
  simp [real_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = forw_ke_forward_id := by
        simpa [ke_sender_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_forward_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          lift_machine_to_type1, forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          lift_machine_to_type1, forw_ke_forward_ids] using
          lifted_forw_has_subroutine_to_sender forw_ke_forward_ids
    · have h_mid : mid = forw_ke_return_id := by
        simpa [ke_sender_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_return_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_return_machine,
          lift_machine_to_type1, forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_return_machine,
          lift_machine_to_type1, forw_ke_return_ids] using
          lifted_forw_has_subroutine_to_receiver forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [protocol_ke_receiver_machine, lift_machine_to_type1,
      ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = forw_ke_forward_id := by
        simpa [ke_receiver_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_forward_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          lift_machine_to_type1, forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          lift_machine_to_type1, forw_ke_forward_ids] using
          lifted_forw_has_subroutine_to_receiver forw_ke_forward_ids
    · have h_mid : mid = forw_ke_return_id := by
        simpa [ke_receiver_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_return_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_return_machine,
          lift_machine_to_type1, forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_return_machine,
          lift_machine_to_type1, forw_ke_return_ids] using
          lifted_forw_has_subroutine_to_sender forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label

theorem real_subroutine_has_matching_caller
    (gen : GroupGenerator) :
  ∀ m ∈ real_machines gen, ∀ mid : MachineId,
    is_subroutine_of_id m.2 mid →
      mid ∈ machine_ids (real_machines gen) →
      ∃ m' ∈ real_machines gen,
        AnyMachine.id m' = mid ∧ is_caller_of_id m'.2 (AnyMachine.id m) := by
  intro m hm mid h_sub h_mid_mem
  simp [real_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = smc_sender_id := by
        simpa [ke_sender_to_smc_sender_port] using h_dest.symm
      subst mid
      rw [machine_ids_real_machines gen] at h_mid_mem
      simp [machine_id_list] at h_mid_mem
      exfalso
      rcases h_mid_mem with h | h | h | h
      · exact smc_sender_ne_ke_sender h
      · exact smc_sender_ne_ke_receiver h
      · exact smc_sender_ne_forw_ke_forward h
      · exact smc_sender_ne_forw_ke_return h
    · cases h_label
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [protocol_ke_receiver_machine, lift_machine_to_type1,
      ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = smc_receiver_id := by
        simpa [ke_receiver_to_smc_receiver_port] using h_dest.symm
      subst mid
      rw [machine_ids_real_machines gen] at h_mid_mem
      simp [machine_id_list] at h_mid_mem
      exfalso
      rcases h_mid_mem with h | h | h | h
      · exact smc_receiver_ne_ke_sender h
      · exact smc_receiver_ne_ke_receiver h
      · exact smc_receiver_ne_forw_ke_forward h
      · exact smc_receiver_ne_forw_ke_return h
    · cases h_label
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = ke_sender_id := by
        simpa [forw_ke_forward_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨ke_sender_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [ke_sender_machine]
    · have h_mid : mid = ke_receiver_id := by
        simpa [forw_ke_forward_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, protocol_ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, protocol_ke_receiver_machine,
          lift_machine_to_type1] using h_mid.symm
      · refine ⟨ke_receiver_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [protocol_ke_receiver_machine, lift_machine_to_type1,
          ke_receiver_machine]
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = ke_receiver_id := by
        simpa [forw_ke_return_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, protocol_ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, protocol_ke_receiver_machine,
          lift_machine_to_type1] using h_mid.symm
      · refine ⟨ke_receiver_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [protocol_ke_receiver_machine, lift_machine_to_type1,
          ke_receiver_machine]
    · have h_mid : mid = ke_sender_id := by
        simpa [forw_ke_return_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨ke_sender_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [ke_sender_machine]
    · cases h_label

theorem real_env_separated
    (gen : GroupGenerator) :
    env_id ∉ machine_ids (real_machines gen) := by
  rw [machine_ids_real_machines gen]
  native_decide

theorem real_adv_separated
    (gen : GroupGenerator) :
    adv_id ∉ machine_ids (real_machines gen) := by
  rw [machine_ids_real_machines gen]
  native_decide

theorem real_no_direct_environment_communication
    (gen : GroupGenerator) :
    ∀ m ∈ real_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest ≠ env_id := by
  intro m hm p hp
  simp [real_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [protocol_ke_receiver_machine, lift_machine_to_type1,
      ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide

theorem real_adversary_communication_is_backdoor
    (gen : GroupGenerator) :
    ∀ m ∈ real_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest = adv_id → p.label = .backdoor := by
  intro m hm p hp h_dest
  simp [real_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;>
      (exfalso; first
        | exact smc_sender_separated.2 (by
            simpa [ke_sender_to_smc_sender_port, mk_subroutine_output_port] using h_dest)
        | exact forw_ke_forward_separated.2 (by
            simpa [ke_sender_to_forw_ke_forward_port, mk_input_port] using h_dest)
        | exact forw_ke_return_separated.2 (by
            simpa [ke_sender_to_forw_ke_return_port, mk_input_port] using h_dest))
  · simp [protocol_ke_receiver_machine, lift_machine_to_type1,
      ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;>
      (exfalso; first
        | exact smc_receiver_separated.2 (by
            simpa [ke_receiver_to_smc_receiver_port, mk_subroutine_output_port] using h_dest)
        | exact forw_ke_forward_separated.2 (by
            simpa [ke_receiver_to_forw_ke_forward_port, mk_input_port] using h_dest)
        | exact forw_ke_return_separated.2 (by
            simpa [ke_receiver_to_forw_ke_return_port, mk_input_port] using h_dest))
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      exact ke_sender_separated.2 (by
        simpa [forw_sender_port, forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest)
    · exfalso
      exact ke_receiver_separated.2 (by
        simpa [forw_receiver_port, forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest)
    · rfl
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      exact ke_receiver_separated.2 (by
        simpa [forw_sender_port, forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest)
    · exfalso
      exact ke_sender_separated.2 (by
        simpa [forw_receiver_port, forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest)
    · rfl

/-- 真实 DHKE protocol：两个 main KE machines 与两个 internal `Forw`。 -/
noncomputable def real_protocol
    (gen : GroupGenerator) : Protocol SMCEasyUCPayload :=
  { machines := real_machines gen
    initial_states := real_initial_states gen
    corruptible_machines := ∅
    unique_ids := real_unique_ids gen
    caller_has_matching_subroutine := real_caller_has_matching_subroutine gen
    subroutine_has_matching_caller := real_subroutine_has_matching_caller gen
    env_separated := real_env_separated gen
    adv_separated := real_adv_separated gen
    no_direct_environment_communication := real_no_direct_environment_communication gen
    adversary_communication_is_backdoor := real_adversary_communication_is_backdoor gen }

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

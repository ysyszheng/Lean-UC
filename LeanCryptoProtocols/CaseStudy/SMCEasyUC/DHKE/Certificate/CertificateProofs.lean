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
    (gen : GroupDescription.{0}) : Machine SMCEasyUCPayload Unit where
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
    (gen : GroupDescription.{0}) : Machine SMCEasyUCPayload Unit where
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

noncomputable def protocol_ke_receiver_machine
    (gen : GroupDescription.{0}) : Machine SMCEasyUCPayload Unit :=
  ke_receiver_machine gen

noncomputable def forw_ke_forward_machine :
    Machine SMCEasyUCPayload Unit :=
  (IdealForw forw_ke_forward_ids).machine

noncomputable def forw_ke_return_machine :
    Machine SMCEasyUCPayload Unit :=
  (IdealForw forw_ke_return_ids).machine

private theorem lifted_forw_has_subroutine_to_sender
    (ids : ForwIds) :
    is_subroutine_of_id (IdealForw ids).machine ids.sender_id := by
  exact forw_has_subroutine_to_sender ids

private theorem lifted_forw_has_subroutine_to_receiver
    (ids : ForwIds) :
    is_subroutine_of_id (IdealForw ids).machine ids.receiver_id := by
  exact forw_has_subroutine_to_receiver ids

/-! ## Real DHKE protocol -/

noncomputable def real_machines
    (gen : GroupDescription.{0}) : List (AnyMachine SMCEasyUCPayload) :=
  [ ⟨Unit, ke_sender_machine gen⟩
  , ⟨Unit, protocol_ke_receiver_machine gen⟩
  , ⟨Unit, forw_ke_forward_machine⟩
  , ⟨Unit, forw_ke_return_machine⟩
  ]

theorem machine_ids_real_machines
    (gen : GroupDescription.{0}) :
    machine_ids (real_machines gen) = machine_id_list := by
  simp [machine_ids, real_machines, machine_id_list, AnyMachine.id,
    ke_sender_machine, protocol_ke_receiver_machine, ke_receiver_machine,
    forw_ke_forward_machine, forw_ke_return_machine,
    IdealForw, Functionality.ForwImpl.machine, forw_ke_forward_ids,
    forw_ke_return_ids]

theorem real_unique_ids
    (gen : GroupDescription.{0}) :
    (machine_ids (real_machines gen)).Nodup := by
  rw [machine_ids_real_machines gen]
  native_decide

theorem real_caller_has_matching_subroutine
    (gen : GroupDescription.{0}) :
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
          forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          forw_ke_forward_ids] using
          lifted_forw_has_subroutine_to_sender forw_ke_forward_ids
    · have h_mid : mid = forw_ke_return_id := by
        simpa [ke_sender_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_return_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_return_machine,
          forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_return_machine,
          forw_ke_return_ids] using
          lifted_forw_has_subroutine_to_receiver forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [protocol_ke_receiver_machine,
      ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = forw_ke_forward_id := by
        simpa [ke_receiver_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_forward_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_forward_machine,
          forw_ke_forward_ids] using
          lifted_forw_has_subroutine_to_receiver forw_ke_forward_ids
    · have h_mid : mid = forw_ke_return_id := by
        simpa [ke_receiver_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, forw_ke_return_machine⟩, ?_, ?_, ?_⟩
      · simp [real_machines]
      · simpa [AnyMachine.id, forw_ke_return_machine,
          forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_return_machine,
          forw_ke_return_ids] using
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
    (gen : GroupDescription.{0}) :
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
    simp [protocol_ke_receiver_machine,
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
          ke_receiver_machine] using h_mid.symm
      · refine ⟨ke_receiver_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [protocol_ke_receiver_machine,
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
          ke_receiver_machine] using h_mid.symm
      · refine ⟨ke_receiver_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [protocol_ke_receiver_machine,
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
    (gen : GroupDescription.{0}) :
    env_id ∉ machine_ids (real_machines gen) := by
  rw [machine_ids_real_machines gen]
  native_decide

theorem real_adv_separated
    (gen : GroupDescription.{0}) :
    adv_id ∉ machine_ids (real_machines gen) := by
  rw [machine_ids_real_machines gen]
  native_decide

theorem real_no_direct_environment_communication
    (gen : GroupDescription.{0}) :
    ∀ m ∈ real_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest ≠ env_id := by
  intro m hm p hp
  simp [real_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [protocol_ke_receiver_machine,
      ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide

/-- 真实 DHKE protocol：两个 main KE machines 与两个 internal `Forw`。 -/
noncomputable def real_protocol
    (gen : GroupDescription.{0}) : Protocol SMCEasyUCPayload :=
  { machines := real_machines gen
    unique_ids := real_unique_ids gen
    caller_has_matching_subroutine := real_caller_has_matching_subroutine gen
    subroutine_has_matching_caller := real_subroutine_has_matching_caller gen
    env_separated := real_env_separated gen
    adv_separated := real_adv_separated gen
    no_direct_environment_communication := real_no_direct_environment_communication gen }

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

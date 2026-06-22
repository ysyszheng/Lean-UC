import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.CertificateObjects

/-!
# SMC EasyUC case study certificate proofs

本文件收纳 certificate 对象的 well-formed 与 protocol-shape 证明。
-/

set_option linter.flexible false
set_option linter.style.nativeDecide false

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Assumptions

noncomputable def smc_sender_machine : Machine SMCEasyUCPayload Unit where
  id := smc_sender_id
  communication_set :=
    { smc_sender_to_ke_sender_port
    , smc_sender_to_forw_smc_port
    , smc_sender_to_external_port
    }
  program := smc_sender_program
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [smc_sender_to_ke_sender_port, smc_sender_to_forw_smc_port,
        smc_sender_to_external_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [smc_sender_to_ke_sender_port, smc_sender_to_forw_smc_port,
        smc_sender_to_external_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (ke_sender_ne_forw_smc
          (by
            simpa [smc_sender_to_ke_sender_port,
              smc_sender_to_forw_smc_port] using h_dest)).elim
      · exact (sender_external_ne_ke_sender
          (by
            simpa [smc_sender_to_ke_sender_port,
              smc_sender_to_external_port] using h_dest.symm)).elim
      · exact (ke_sender_ne_forw_smc
          (by
            simpa [smc_sender_to_ke_sender_port,
              smc_sender_to_forw_smc_port] using h_dest.symm)).elim
      · rfl
      · exact (sender_external_ne_forw_smc
          (by
            simpa [smc_sender_to_forw_smc_port,
              smc_sender_to_external_port] using h_dest.symm)).elim
      · exact (sender_external_ne_ke_sender
          (by
            simpa [smc_sender_to_ke_sender_port,
              smc_sender_to_external_port] using h_dest)).elim
      · exact (sender_external_ne_forw_smc
          (by
            simpa [smc_sender_to_forw_smc_port,
              smc_sender_to_external_port] using h_dest)).elim
      · rfl

noncomputable def smc_receiver_machine : Machine SMCEasyUCPayload Unit where
  id := smc_receiver_id
  communication_set :=
    { smc_receiver_to_ke_receiver_port
    , smc_receiver_to_forw_smc_port
    , smc_receiver_to_external_port
    }
  program := smc_receiver_program
  well_formed := by
    classical
    refine ⟨?_, ?_⟩
    · intro p hp
      simp [smc_receiver_to_ke_receiver_port, smc_receiver_to_forw_smc_port,
        smc_receiver_to_external_port] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    · intro p₁ hp₁ p₂ hp₂ h_dest
      simp [smc_receiver_to_ke_receiver_port, smc_receiver_to_forw_smc_port,
        smc_receiver_to_external_port] at hp₁ hp₂
      rcases hp₁ with rfl | rfl | rfl <;> rcases hp₂ with rfl | rfl | rfl
      · rfl
      · exact (ke_receiver_ne_forw_smc
          (by
            simpa [smc_receiver_to_ke_receiver_port,
              smc_receiver_to_forw_smc_port] using h_dest)).elim
      · exact (receiver_external_ne_ke_receiver
          (by
            simpa [smc_receiver_to_ke_receiver_port,
              smc_receiver_to_external_port] using h_dest.symm)).elim
      · exact (ke_receiver_ne_forw_smc
          (by
            simpa [smc_receiver_to_ke_receiver_port,
              smc_receiver_to_forw_smc_port] using h_dest.symm)).elim
      · rfl
      · exact (receiver_external_ne_forw_smc
          (by
            simpa [smc_receiver_to_forw_smc_port,
              smc_receiver_to_external_port] using h_dest.symm)).elim
      · exact (receiver_external_ne_ke_receiver
          (by
            simpa [smc_receiver_to_ke_receiver_port,
              smc_receiver_to_external_port] using h_dest)).elim
      · exact (receiver_external_ne_forw_smc
          (by
            simpa [smc_receiver_to_forw_smc_port,
              smc_receiver_to_external_port] using h_dest)).elim
      · rfl

noncomputable def ke_sender_machine
    (gen : GroupGenerator) : Machine SMCEasyUCPayload Unit where
  id := ke_sender_id
  communication_set :=
    { ke_sender_to_smc_sender_port
    , ke_sender_to_forw_ke_forward_port
    , ke_sender_to_forw_ke_return_port
    }
  program := ke_sender_program gen
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
  program := ke_receiver_program gen
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

private theorem ke_sender_is_subroutine_of_smc_sender
    (gen : GroupGenerator) :
    is_subroutine_of_id (ke_sender_machine gen) smc_sender_id := by
  refine ⟨ke_sender_to_smc_sender_port, ?_, rfl, rfl⟩
  simp [ke_sender_machine]

private theorem ke_receiver_is_subroutine_of_smc_receiver
    (gen : GroupGenerator) :
    is_subroutine_of_id (ke_receiver_machine gen) smc_receiver_id := by
  refine ⟨ke_receiver_to_smc_receiver_port, ?_, rfl, rfl⟩
  simp [ke_receiver_machine]

/-! ## Protocol -/

noncomputable def real_smc_machines
    (gen : GroupGenerator) : List (AnyMachine SMCEasyUCPayload) :=
  [ ⟨Unit, smc_sender_machine⟩
  , ⟨Unit, smc_receiver_machine⟩
  , ⟨Unit, ke_sender_machine gen⟩
  , ⟨Unit, ke_receiver_machine gen⟩
  , ⟨Unit, (IdealForw forw_ke_forward_ids).machine⟩
  , ⟨Unit, (IdealForw forw_ke_return_ids).machine⟩
  , ⟨Unit, (IdealForw forw_smc_ids).machine⟩
  ]

theorem real_smc_unique_ids
    (gen : GroupGenerator) :
    (machine_ids (real_smc_machines gen)).Nodup := by
  change
    [ smc_sender_id
    , smc_receiver_id
    , ke_sender_id
    , ke_receiver_id
    , forw_ke_forward_id
    , forw_ke_return_id
    , forw_smc_id
    ].Nodup
  native_decide

theorem real_smc_caller_has_matching_subroutine
    (gen : GroupGenerator) :
  ∀ m ∈ real_smc_machines gen, ∀ mid : MachineId,
    is_caller_of_id m.2 mid →
      ∃ m' ∈ real_smc_machines gen,
        AnyMachine.id m' = mid ∧ is_subroutine_of_id m'.2 (AnyMachine.id m) := by
  intro m hm mid h_caller
  simp [real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [smc_sender_machine, smc_sender_to_ke_sender_port,
      smc_sender_to_forw_smc_port, smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = ke_sender_id := by
        simpa [smc_sender_to_ke_sender_port] using h_dest.symm
      refine ⟨⟨Unit, ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · simpa [AnyMachine.id] using ke_sender_is_subroutine_of_smc_sender gen
    · have h_mid : mid = forw_smc_id := by
        simpa [smc_sender_to_forw_smc_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw forw_smc_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id, forw_smc_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_smc_ids] using
          forw_has_subroutine_to_sender forw_smc_ids
    · cases h_label
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [smc_receiver_machine, smc_receiver_to_ke_receiver_port,
      smc_receiver_to_forw_smc_port, smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = ke_receiver_id := by
        simpa [smc_receiver_to_ke_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · simpa [AnyMachine.id] using ke_receiver_is_subroutine_of_smc_receiver gen
    · have h_mid : mid = forw_smc_id := by
        simpa [smc_receiver_to_forw_smc_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw forw_smc_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id, forw_smc_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_smc_ids] using
          forw_has_subroutine_to_receiver forw_smc_ids
    · cases h_label
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = forw_ke_forward_id := by
        simpa [ke_sender_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw forw_ke_forward_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id, forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_forward_ids] using
          forw_has_subroutine_to_sender forw_ke_forward_ids
    · have h_mid : mid = forw_ke_return_id := by
        simpa [ke_sender_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw forw_ke_return_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id, forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_return_ids] using
          forw_has_subroutine_to_receiver forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, h_dest, h_label⟩
    simp [ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · have h_mid : mid = forw_ke_forward_id := by
        simpa [ke_receiver_to_forw_ke_forward_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw forw_ke_forward_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id, forw_ke_forward_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_forward_ids] using
          forw_has_subroutine_to_receiver forw_ke_forward_ids
    · have h_mid : mid = forw_ke_return_id := by
        simpa [ke_receiver_to_forw_ke_return_port] using h_dest.symm
      refine ⟨⟨Unit, (IdealForw forw_ke_return_ids).machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id, forw_ke_return_ids, IdealForw] using h_mid.symm
      · simpa [AnyMachine.id, forw_ke_return_ids] using
          forw_has_subroutine_to_sender forw_ke_return_ids
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label
  · rcases h_caller with ⟨p, hp, _h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> cases h_label

theorem real_smc_subroutine_has_matching_caller
    (gen : GroupGenerator) :
  ∀ m ∈ real_smc_machines gen, ∀ mid : MachineId,
    is_subroutine_of_id m.2 mid →
      mid ∈ machine_ids (real_smc_machines gen) →
      ∃ m' ∈ real_smc_machines gen,
        AnyMachine.id m' = mid ∧ is_caller_of_id m'.2 (AnyMachine.id m) := by
  intro m hm mid h_sub h_mid_mem
  simp [real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [smc_sender_machine, smc_sender_to_ke_sender_port,
      smc_sender_to_forw_smc_port, smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · cases h_label
    · have h_mid : mid = sender_external_id := by
        simpa [smc_sender_to_external_port] using h_dest.symm
      subst mid
      change sender_external_id ∈ machine_id_list at h_mid_mem
      simp [machine_id_list] at h_mid_mem
      exfalso
      rcases h_mid_mem with h | h | h | h | h | h | h
      · exact sender_external_ne_smc_sender h
      · exact sender_external_ne_smc_receiver h
      · exact sender_external_ne_ke_sender h
      · exact sender_external_ne_ke_receiver h
      · exact sender_external_ne_forw_ke_forward h
      · exact sender_external_ne_forw_ke_return h
      · exact sender_external_ne_forw_smc h
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [smc_receiver_machine, smc_receiver_to_ke_receiver_port,
      smc_receiver_to_forw_smc_port, smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · cases h_label
    · cases h_label
    · have h_mid : mid = receiver_external_id := by
        simpa [smc_receiver_to_external_port] using h_dest.symm
      subst mid
      change receiver_external_id ∈ machine_id_list at h_mid_mem
      simp [machine_id_list] at h_mid_mem
      exfalso
      rcases h_mid_mem with h | h | h | h | h | h | h
      · exact receiver_external_ne_smc_sender h
      · exact receiver_external_ne_smc_receiver h
      · exact receiver_external_ne_ke_sender h
      · exact receiver_external_ne_ke_receiver h
      · exact receiver_external_ne_forw_ke_forward h
      · exact receiver_external_ne_forw_ke_return h
      · exact receiver_external_ne_forw_smc h
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = smc_sender_id := by
        simpa [ke_sender_to_smc_sender_port] using h_dest.symm
      refine ⟨⟨Unit, smc_sender_machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨smc_sender_to_ke_sender_port, ?_, rfl, rfl⟩
        simp [smc_sender_machine]
    · cases h_label
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    simp [ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = smc_receiver_id := by
        simpa [ke_receiver_to_smc_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, smc_receiver_machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨smc_receiver_to_ke_receiver_port, ?_, rfl, rfl⟩
        simp [smc_receiver_machine]
    · cases h_label
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = ke_sender_id := by
        simpa [forw_ke_forward_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨ke_sender_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [ke_sender_machine]
    · have h_mid : mid = ke_receiver_id := by
        simpa [forw_ke_forward_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨ke_receiver_to_forw_ke_forward_port, ?_, rfl, rfl⟩
        simp [ke_receiver_machine]
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = ke_receiver_id := by
        simpa [forw_ke_return_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, ke_receiver_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨ke_receiver_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [ke_receiver_machine]
    · have h_mid : mid = ke_sender_id := by
        simpa [forw_ke_return_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, ke_sender_machine gen⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨ke_sender_to_forw_ke_return_port, ?_, rfl, rfl⟩
        simp [ke_sender_machine]
    · cases h_label
  · rcases h_sub with ⟨p, hp, h_dest, h_label⟩
    change p ∈ Functionality.ForwImpl.communication_set forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · have h_mid : mid = smc_sender_id := by
        simpa [forw_smc_ids, forw_sender_port] using h_dest.symm
      refine ⟨⟨Unit, smc_sender_machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨smc_sender_to_forw_smc_port, ?_, rfl, rfl⟩
        simp [smc_sender_machine]
    · have h_mid : mid = smc_receiver_id := by
        simpa [forw_smc_ids, forw_receiver_port] using h_dest.symm
      refine ⟨⟨Unit, smc_receiver_machine⟩, ?_, ?_, ?_⟩
      · simp [real_smc_machines]
      · simpa [AnyMachine.id] using h_mid.symm
      · refine ⟨smc_receiver_to_forw_smc_port, ?_, rfl, rfl⟩
        simp [smc_receiver_machine]
    · cases h_label

theorem real_smc_env_separated
    (gen : GroupGenerator) :
    env_id ∉ machine_ids (real_smc_machines gen) := by
  change env_id ∉ machine_id_list
  native_decide

theorem real_smc_adv_separated
    (gen : GroupGenerator) :
    adv_id ∉ machine_ids (real_smc_machines gen) := by
  change adv_id ∉ machine_id_list
  native_decide

theorem real_smc_no_direct_environment_communication
    (gen : GroupGenerator) :
    ∀ m ∈ real_smc_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest ≠ env_id := by
  intro m hm p hp
  simp [real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [smc_sender_machine, smc_sender_to_ke_sender_port,
      smc_sender_to_forw_smc_port, smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [smc_receiver_machine, smc_receiver_to_ke_receiver_port,
      smc_receiver_to_forw_smc_port, smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · simp [ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · change p ∈ Functionality.ForwImpl.communication_set forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl <;> decide

theorem real_smc_adversary_communication_is_backdoor
    (gen : GroupGenerator) :
    ∀ m ∈ real_smc_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest = adv_id → p.label = .backdoor := by
  intro m hm p hp h_dest
  simp [real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [smc_sender_machine, smc_sender_to_ke_sender_port,
      smc_sender_to_forw_smc_port, smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_sender_id = adv_id := by
        simpa [smc_sender_to_ke_sender_port, mk_input_port] using h_dest
      exact ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : forw_smc_id = adv_id := by
        simpa [smc_sender_to_forw_smc_port, mk_input_port] using h_dest
      exact forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : sender_external_id = adv_id := by
        simpa [smc_sender_to_external_port, mk_subroutine_output_port] using h_dest
      exact sender_external_separated.2 h_bad
  · simp [smc_receiver_machine, smc_receiver_to_ke_receiver_port,
      smc_receiver_to_forw_smc_port, smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_receiver_id = adv_id := by
        simpa [smc_receiver_to_ke_receiver_port, mk_input_port] using h_dest
      exact ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : forw_smc_id = adv_id := by
        simpa [smc_receiver_to_forw_smc_port, mk_input_port] using h_dest
      exact forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : receiver_external_id = adv_id := by
        simpa [smc_receiver_to_external_port, mk_subroutine_output_port] using h_dest
      exact receiver_external_separated.2 h_bad
  · simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : smc_sender_id = adv_id := by
        simpa [ke_sender_to_smc_sender_port, mk_subroutine_output_port] using h_dest
      exact smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_forward_id = adv_id := by
        simpa [ke_sender_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_return_id = adv_id := by
        simpa [ke_sender_to_forw_ke_return_port, mk_input_port] using h_dest
      exact forw_ke_return_separated.2 h_bad
  · simp [ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : smc_receiver_id = adv_id := by
        simpa [ke_receiver_to_smc_receiver_port, mk_subroutine_output_port] using h_dest
      exact smc_receiver_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_forward_id = adv_id := by
        simpa [ke_receiver_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_return_id = adv_id := by
        simpa [ke_receiver_to_forw_ke_return_port, mk_input_port] using h_dest
      exact forw_ke_return_separated.2 h_bad
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_sender_id = adv_id := by
        simpa [forw_sender_port, forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : ke_receiver_id = adv_id := by
        simpa [forw_receiver_port, forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_receiver_separated.2 h_bad
    · rfl
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_receiver_id = adv_id := by
        simpa [forw_sender_port, forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : ke_sender_id = adv_id := by
        simpa [forw_receiver_port, forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_sender_separated.2 h_bad
    · rfl
  · change p ∈ Functionality.ForwImpl.communication_set forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : smc_sender_id = adv_id := by
        simpa [forw_sender_port, forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : smc_receiver_id = adv_id := by
        simpa [forw_receiver_port, forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact smc_receiver_separated.2 h_bad
    · rfl

/-- 审计约束：real-world 中显式连向 adversary 的 backdoor 只来自三个 `Forw` functionality。 -/
theorem adversary_backdoor_targets_are_forw
    (gen : GroupGenerator) :
    ∀ m ∈ real_smc_machines gen, ∀ p ∈ m.2.communication_set,
      p.dest = adv_id → AnyMachine.id m ∈ forw_control_targets := by
  intro m hm p hp h_dest
  simp [real_smc_machines] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [smc_sender_machine, smc_sender_to_ke_sender_port,
      smc_sender_to_forw_smc_port, smc_sender_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_sender_id = adv_id := by
        simpa [smc_sender_to_ke_sender_port, mk_input_port] using h_dest
      exact ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : forw_smc_id = adv_id := by
        simpa [smc_sender_to_forw_smc_port, mk_input_port] using h_dest
      exact forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : sender_external_id = adv_id := by
        simpa [smc_sender_to_external_port, mk_subroutine_output_port] using h_dest
      exact sender_external_separated.2 h_bad
  · simp [smc_receiver_machine, smc_receiver_to_ke_receiver_port,
      smc_receiver_to_forw_smc_port, smc_receiver_to_external_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_receiver_id = adv_id := by
        simpa [smc_receiver_to_ke_receiver_port, mk_input_port] using h_dest
      exact ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : forw_smc_id = adv_id := by
        simpa [smc_receiver_to_forw_smc_port, mk_input_port] using h_dest
      exact forw_smc_separated.2 h_bad
    · exfalso
      have h_bad : receiver_external_id = adv_id := by
        simpa [smc_receiver_to_external_port, mk_subroutine_output_port] using h_dest
      exact receiver_external_separated.2 h_bad
  · simp [ke_sender_machine, ke_sender_to_smc_sender_port,
      ke_sender_to_forw_ke_forward_port, ke_sender_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : smc_sender_id = adv_id := by
        simpa [ke_sender_to_smc_sender_port, mk_subroutine_output_port] using h_dest
      exact smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_forward_id = adv_id := by
        simpa [ke_sender_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_return_id = adv_id := by
        simpa [ke_sender_to_forw_ke_return_port, mk_input_port] using h_dest
      exact forw_ke_return_separated.2 h_bad
  · simp [ke_receiver_machine, ke_receiver_to_smc_receiver_port,
      ke_receiver_to_forw_ke_forward_port, ke_receiver_to_forw_ke_return_port] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : smc_receiver_id = adv_id := by
        simpa [ke_receiver_to_smc_receiver_port, mk_subroutine_output_port] using h_dest
      exact smc_receiver_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_forward_id = adv_id := by
        simpa [ke_receiver_to_forw_ke_forward_port, mk_input_port] using h_dest
      exact forw_ke_forward_separated.2 h_bad
    · exfalso
      have h_bad : forw_ke_return_id = adv_id := by
        simpa [ke_receiver_to_forw_ke_return_port, mk_input_port] using h_dest
      exact forw_ke_return_separated.2 h_bad
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_forward_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_sender_id = adv_id := by
        simpa [forw_sender_port, forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_sender_separated.2 h_bad
    · exfalso
      have h_bad : ke_receiver_id = adv_id := by
        simpa [forw_receiver_port, forw_ke_forward_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_receiver_separated.2 h_bad
    · change forw_ke_forward_id ∈ forw_control_targets
      simp [forw_control_targets]
  · change p ∈ Functionality.ForwImpl.communication_set forw_ke_return_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : ke_receiver_id = adv_id := by
        simpa [forw_sender_port, forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_receiver_separated.2 h_bad
    · exfalso
      have h_bad : ke_sender_id = adv_id := by
        simpa [forw_receiver_port, forw_ke_return_ids,
          mk_subroutine_output_port] using h_dest
      exact ke_sender_separated.2 h_bad
    · change forw_ke_return_id ∈ forw_control_targets
      simp [forw_control_targets]
  · change p ∈ Functionality.ForwImpl.communication_set forw_smc_ids at hp
    simp [Functionality.ForwImpl.communication_set] at hp
    rcases hp with rfl | rfl | rfl
    · exfalso
      have h_bad : smc_sender_id = adv_id := by
        simpa [forw_sender_port, forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact smc_sender_separated.2 h_bad
    · exfalso
      have h_bad : smc_receiver_id = adv_id := by
        simpa [forw_receiver_port, forw_smc_ids,
          mk_subroutine_output_port] using h_dest
      exact smc_receiver_separated.2 h_bad
    · change forw_smc_id ∈ forw_control_targets
      simp [forw_control_targets]

/-- 审计入口暴露的 real SMC protocol：2 个 main machines 与 5 个 internal machines。 -/
noncomputable def real_smc_protocol
    (gen : GroupGenerator) : Protocol SMCEasyUCPayload :=
  { machines := real_smc_machines gen
    corruptible_machines := ∅
    unique_ids := real_smc_unique_ids gen
    caller_has_matching_subroutine :=
      real_smc_caller_has_matching_subroutine gen
    subroutine_has_matching_caller :=
      real_smc_subroutine_has_matching_caller gen
    env_separated := real_smc_env_separated gen
    adv_separated := real_smc_adv_separated gen
    no_direct_environment_communication :=
      real_smc_no_direct_environment_communication gen
    adversary_communication_is_backdoor :=
      real_smc_adversary_communication_is_backdoor gen }
/-- 两个 main machines 正是 SMC sender / receiver。 -/
theorem smc_sender_is_main
    (gen : GroupGenerator) :
    (real_smc_protocol gen).is_main_machine smc_sender_id := by
  refine ⟨⟨Unit, smc_sender_machine⟩, ?_, rfl, ?_⟩
  · simp [real_smc_protocol, real_smc_machines]
  · refine ⟨sender_external_id, ?_, ?_, ?_⟩
    · simp [real_smc_protocol, real_smc_machines]
    · refine ⟨smc_sender_to_external_port, ?_, rfl, rfl⟩
      simp [smc_sender_machine]
    · change sender_external_id ∉ machine_id_list
      native_decide

theorem smc_receiver_is_main
    (gen : GroupGenerator) :
    (real_smc_protocol gen).is_main_machine smc_receiver_id := by
  refine ⟨⟨Unit, smc_receiver_machine⟩, ?_, rfl, ?_⟩
  · simp [real_smc_protocol, real_smc_machines]
  · refine ⟨receiver_external_id, ?_, ?_, ?_⟩
    · simp [real_smc_protocol, real_smc_machines]
    · refine ⟨smc_receiver_to_external_port, ?_, rfl, rfl⟩
      simp [smc_receiver_machine]
    · change receiver_external_id ∉ machine_id_list
      native_decide

end LeanCryptoProtocols.CaseStudy.SMCEasyUC

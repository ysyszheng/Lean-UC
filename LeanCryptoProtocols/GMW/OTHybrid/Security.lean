import LeanCryptoProtocols.GMW.OTHybrid.Model
import LeanCryptoProtocols.UC.Functionality.OT
import LeanCryptoProtocols.UC.Functionality.SFE
import LeanCryptoProtocols.Circuit.BoolCircuit

/-!
# OT-hybrid 世界中的 GMW 安全证明

本文件放置 GMW 在 OT-hybrid world 下的详细 simulator 构造与 UC 安全证明。

审核者默认不需要先读这里；本文件面向证明实现者。审计入口在 `Certificate.lean`。
-/

namespace LeanCryptoProtocols.GMW.OTHybrid

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Circuit

/-- XOR 门在 real / ideal 中对单边视图的更新是一致的。 -/
theorem xor_gate_view_sim (gateId : Nat) (lhs rhs : Bool) :
    LeftEvent.xor gateId lhs rhs (bxor lhs rhs) =
      LeftEvent.xor gateId lhs rhs (bxor lhs rhs) := by
  rfl

/-- NOT 门在 real / ideal 中对单边视图的更新是一致的。 -/
theorem not_gate_view_sim (gateId : Nat) (inp : Bool) :
    LeftEvent.not gateId inp (!inp) = LeftEvent.not gateId inp (!inp) := by
  rfl

/-- 左方被腐化时，AND 门的局部视图只依赖左方份额与独立采样的两位随机量。 -/
theorem and_gate_view_sim_left
    (gateId : Nat) (lhs rhs sendMask recvOut : Bool) :
    LeftEvent.and gateId lhs rhs
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (receiverView gateId rhs recvOut)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) =
      LeftEvent.and gateId lhs rhs
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (receiverView gateId rhs recvOut)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) := by
  rfl

/-- 右方被腐化时，AND 门的局部视图只依赖右方份额与独立采样的两位随机量。 -/
theorem and_gate_view_sim_right
    (gateId : Nat) (lhs rhs recvOut sendMask : Bool) :
    RightEvent.and gateId lhs rhs
        (receiverView gateId rhs recvOut)
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) =
      RightEvent.and gateId lhs rhs
        (receiverView gateId rhs recvOut)
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) := by
  rfl

/-- GMW 在 OT-hybrid 世界中的模拟器。 -/
noncomputable def gmwSimulator {Adv : Type} (c : BoolCircuit) :
    Adv → Simulator (IdealBoolCircuitSFE c).interface PartyView
  | _ =>
      fun corr cin cout _ =>
        match corr with
        | .none => constFamily (PMF.pure Internal.blankLocalView)
        | .left =>
            constFamily <|
              PMF.map
                (fun seed => Internal.leftOnlyLocalView (Internal.leftSimView c cin cout seed))
                (Internal.uniformDist (Internal.LeftSeed c))
        | .right =>
            constFamily <|
              PMF.map
                (fun seed => Internal.rightOnlyLocalView (Internal.rightSimView c cin cout seed))
                (Internal.uniformDist (Internal.RightSeed c))
        | .both =>
            constFamily <|
              PMF.map (Internal.bothSimView c cin) (Internal.uniformDist (Internal.BothSeed c))

/-- 左方情形下，真实视图生成器与模拟视图生成器完全一致。 -/
theorem left_real_eq_sim (c : BoolCircuit) (input : Inputs c) (seed : Internal.LeftSeed c) :
    Internal.leftRealView c input seed = Internal.leftSimView c input.left (c.eval input) seed := by
  rfl

/-- 右方情形下，真实视图生成器与模拟视图生成器完全一致。 -/
theorem right_real_eq_sim (c : BoolCircuit) (input : Inputs c) (seed : Internal.RightSeed c) :
    Internal.rightRealView c input seed =
      Internal.rightSimView c input.right (c.eval input) seed := by
  rfl

/-- 单个腐化情形下的完美不可区分。 -/
theorem gmw_case_perfect {Adv : Type} (c : BoolCircuit) (adv : Adv)
    (corr : CorruptionCase) (input : Inputs c) :
    Indistinguishable .perfect zeroError (fun _ => True) (env := { run := fun _ => false })
      (RealModel (realProtocol (Adv := Adv) c) corr adv input)
      (IdealModel (IdealBoolCircuitSFE c) ((gmwSimulator (Adv := Adv) c) adv) corr input) := by
  cases corr with
  | none =>
      intro n
      simp [RealModel, IdealModel, realProtocol, gmwSimulator, ObservedDist]
  | left =>
      intro n
      change
        PMF.map (observedView CorruptionCase.left)
          (PMF.map
            (fun seed =>
              Internal.leftOnlyLocalView (Internal.leftRealView c input seed))
            (Internal.uniformDist (Internal.LeftSeed c))) =
        PMF.map (observedView CorruptionCase.left)
          (PMF.map
            (fun seed =>
              Internal.leftOnlyLocalView
                (Internal.leftSimView c input.left (c.eval input) seed))
            (Internal.uniformDist (Internal.LeftSeed c)))
      simp [left_real_eq_sim]
  | right =>
      intro n
      change
        PMF.map (observedView CorruptionCase.right)
          (PMF.map
            (fun seed =>
              Internal.rightOnlyLocalView (Internal.rightRealView c input seed))
            (Internal.uniformDist (Internal.RightSeed c))) =
        PMF.map (observedView CorruptionCase.right)
          (PMF.map
            (fun seed =>
              Internal.rightOnlyLocalView
                (Internal.rightSimView c input.right (c.eval input) seed))
            (Internal.uniformDist (Internal.RightSeed c)))
      simp [right_real_eq_sim]
  | both =>
      intro n
      change
        PMF.map (observedView CorruptionCase.both)
          (PMF.map (Internal.bothRealView c input) (Internal.uniformDist (Internal.BothSeed c))) =
        PMF.map (observedView CorruptionCase.both)
          (PMF.map (Internal.bothRealView c input) (Internal.uniformDist (Internal.BothSeed c)))
      rfl

/-- 真实世界与理想世界的观察分布在四种腐化情形下都完全一致。 -/
theorem gmw_real_ideal_view_eq {Adv : Type} (c : BoolCircuit) :
    ∀ adv corr input,
      PerfectIndist
        (RealModel (realProtocol (Adv := Adv) c) corr adv input)
        (IdealModel (IdealBoolCircuitSFE c) ((gmwSimulator (Adv := Adv) c) adv) corr input) := by
  intro adv corr input
  simpa [Indistinguishable] using
    (gmw_case_perfect (Adv := Adv) c adv corr input)

/-- OT-hybrid 世界中 GMW 的严格完美 UC 安全性。 -/
theorem gmw_ot_hybrid_uc_secure_perfect {Adv : Type} (c : BoolCircuit) :
    UCSecurePerfect (realProtocol (Adv := Adv) c) (IdealBoolCircuitSFE c) := by
  refine UCSecureAt.of_cases
    (level := .perfect)
    (ε := zeroError)
    (PPTEnv := fun _ => True)
    (protocol := realProtocol (Adv := Adv) c)
    (ideal := IdealBoolCircuitSFE c)
    (simulatorFor := gmwSimulator (Adv := Adv) c)
    ?_ ?_ ?_ ?_
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .none input
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .left input
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .right input
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .both input

/-- 向后兼容的名字。 -/
theorem gmw_ot_hybrid_uc_secure {Adv : Type} (c : BoolCircuit) :
    UCSecurePerfect (realProtocol (Adv := Adv) c) (IdealBoolCircuitSFE c) :=
  gmw_ot_hybrid_uc_secure_perfect (Adv := Adv) c

end LeanCryptoProtocols.GMW.OTHybrid

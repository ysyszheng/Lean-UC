import Mathlib
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# 三层不可区分接口

本文件把执行结果看作环境输出 bit 的分布族，并给出：

- 完美不可区分；
- 统计不可区分；
- 计算不可区分；

以及这些定义之间的基础关系与闭包引理。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- 带辅助输入与安全参数的执行 ensemble。 -/
abbrev Ensemble (Aux : Type u) : Type u := Aux → ℕ → PMF Bool

/-- 计算安全层沿用 mathlib 的超多项式衰减接口。 -/
def Negligible (f : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) f

/-- 三种安全级别。 -/
inductive SecurityLevel where
  | perfect
  | statistical
  | computational
  deriving DecidableEq, Repr

/-- 分布输出 `true` 的概率。 -/
noncomputable def probTrue (d : PMF Bool) : ℝ :=
  ENNReal.toReal (d true)

/-- 两个执行 ensemble 在辅助输入 `z`、安全参数 `n` 下的区分优势。 -/
noncomputable def Advantage {Aux : Type u}
    (X Y : Ensemble Aux) (z : Aux) (n : ℕ) : ℝ :=
  |probTrue (X z n) - probTrue (Y z n)|

/-- 完美不可区分：逐点完全相等。 -/
def PerfectIndist {Aux : Type u} (X Y : Ensemble Aux) : Prop :=
  ∀ z n, X z n = Y z n

/-- 统计不可区分：优势被显式误差函数上界。 -/
def StatisticalIndist {Aux : Type u}
    (ε : ℕ → ℝ) (X Y : Ensemble Aux) : Prop :=
  ∀ z n, Advantage X Y z n ≤ ε n

/-- 计算不可区分：对每个辅助输入，优势函数可忽略。 -/
def ComputationalIndist {Aux : Type u} (X Y : Ensemble Aux) : Prop :=
  ∀ z, Negligible (fun n => Advantage X Y z n)

/-- 统一的三层不可区分接口。 -/
def Indistinguishable {Aux : Type u}
    (level : SecurityLevel) (ε : ℕ → ℝ) (X Y : Ensemble Aux) : Prop :=
  match level with
  | .perfect => PerfectIndist X Y
  | .statistical => StatisticalIndist ε X Y
  | .computational => ComputationalIndist X Y

/-- 默认零误差函数。 -/
def zeroError : ℕ → ℝ := fun _ => 0

@[simp] theorem Advantage_nonneg {Aux : Type u}
    (X Y : Ensemble Aux) (z : Aux) (n : ℕ) : 0 ≤ Advantage X Y z n := by
  simp [Advantage]

theorem Advantage_eq_zero_of_eq {Aux : Type u}
    {X Y : Ensemble Aux} (h : X = Y) (z : Aux) (n : ℕ) :
    Advantage X Y z n = 0 := by
  subst h
  simp [Advantage]

theorem Advantage_comm {Aux : Type u}
    (X Y : Ensemble Aux) (z : Aux) (n : ℕ) :
    Advantage X Y z n = Advantage Y X z n := by
  simp [Advantage, abs_sub_comm]

theorem Advantage_triangle {Aux : Type u}
    (X Y Z : Ensemble Aux) (z : Aux) (n : ℕ) :
    Advantage X Z z n ≤ Advantage X Y z n + Advantage Y Z z n := by
  dsimp [Advantage, probTrue]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    abs_sub_le
      (ENNReal.toReal (X z n true))
      (ENNReal.toReal (Y z n true))
      (ENNReal.toReal (Z z n true))

theorem PerfectIndist.refl {Aux : Type u} (X : Ensemble Aux) : PerfectIndist X X := by
  intro z n
  rfl

theorem PerfectIndist.symm {Aux : Type u} {X Y : Ensemble Aux} :
    PerfectIndist X Y → PerfectIndist Y X := by
  intro h z n
  symm
  exact h z n

theorem PerfectIndist.trans {Aux : Type u} {X Y Z : Ensemble Aux} :
    PerfectIndist X Y → PerfectIndist Y Z → PerfectIndist X Z := by
  intro hXY hYZ z n
  rw [hXY z n, hYZ z n]

theorem StatisticalIndist.refl {Aux : Type u} (X : Ensemble Aux) :
    StatisticalIndist zeroError X X := by
  intro z n
  simpa [zeroError] using le_of_eq (Advantage_eq_zero_of_eq rfl z n)

theorem StatisticalIndist.symm {Aux : Type u} {ε : ℕ → ℝ} {X Y : Ensemble Aux} :
    StatisticalIndist ε X Y → StatisticalIndist ε Y X := by
  intro h z n
  simpa [Advantage_comm] using h z n

theorem StatisticalIndist.trans {Aux : Type u}
    {ε₁ ε₂ : ℕ → ℝ} {X Y Z : Ensemble Aux}
    (hXY : StatisticalIndist ε₁ X Y)
    (hYZ : StatisticalIndist ε₂ Y Z) :
    StatisticalIndist (fun n => ε₁ n + ε₂ n) X Z := by
  intro z n
  calc
    Advantage X Z z n ≤ Advantage X Y z n + Advantage Y Z z n :=
      Advantage_triangle X Y Z z n
    _ ≤ ε₁ n + ε₂ n := add_le_add (hXY z n) (hYZ z n)

theorem PerfectIndist.statistical {Aux : Type u} {X Y : Ensemble Aux}
    (h : PerfectIndist X Y) :
    StatisticalIndist zeroError X Y := by
  intro z n
  have h' : Advantage X Y z n = 0 := by
    simp [Advantage, h z n]
  simpa [zeroError] using le_of_eq h'

theorem Negligible.zero : Negligible (fun _ : ℕ => (0 : ℝ)) :=
  Asymptotics.superpolynomialDecay_zero Filter.atTop (fun n : ℕ => (n : ℝ))

theorem Negligible.add {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun n => f n + g n) :=
  Asymptotics.SuperpolynomialDecay.add hf hg

theorem Negligible.const_mul {f : ℕ → ℝ} (hf : Negligible f) (c : ℝ) :
    Negligible (fun n => c * f n) :=
  Asymptotics.SuperpolynomialDecay.const_mul hf c

theorem Negligible.of_abs_le {f g : ℕ → ℝ}
    (hg : Negligible g) (hfg : ∀ n, |f n| ≤ |g n|) :
    Negligible f :=
  Asymptotics.SuperpolynomialDecay.trans_abs_le hg hfg

theorem ComputationalIndist.refl {Aux : Type u} (X : Ensemble Aux) :
    ComputationalIndist X X := by
  intro z
  have hzero : (fun n => Advantage X X z n) = fun _ => (0 : ℝ) := by
    funext n
    simp [Advantage]
  rw [hzero]
  exact Negligible.zero

theorem ComputationalIndist.symm {Aux : Type u} {X Y : Ensemble Aux} :
    ComputationalIndist X Y → ComputationalIndist Y X := by
  intro h z
  refine Negligible.of_abs_le (h z) ?_
  intro n
  simp [Advantage_comm]

theorem ComputationalIndist.trans {Aux : Type u} {X Y Z : Ensemble Aux}
    (hXY : ComputationalIndist X Y)
    (hYZ : ComputationalIndist Y Z) :
    ComputationalIndist X Z := by
  intro z
  have hsum : Negligible (fun n => Advantage X Y z n + Advantage Y Z z n) :=
    Negligible.add (hXY z) (hYZ z)
  refine Negligible.of_abs_le hsum ?_
  intro n
  have htri := Advantage_triangle X Y Z z n
  have hnonneg₁ : 0 ≤ Advantage X Z z n := Advantage_nonneg X Z z n
  have hnonneg₂ : 0 ≤ Advantage X Y z n + Advantage Y Z z n := by
    exact add_nonneg (Advantage_nonneg X Y z n) (Advantage_nonneg Y Z z n)
  simpa [abs_of_nonneg hnonneg₁, abs_of_nonneg hnonneg₂] using htri

theorem PerfectIndist.computational {Aux : Type u} {X Y : Ensemble Aux}
    (h : PerfectIndist X Y) :
    ComputationalIndist X Y := by
  intro z
  have hzero : (fun n => Advantage X Y z n) = fun _ => (0 : ℝ) := by
    funext n
    simp [Advantage, h z n]
  rw [hzero]
  exact Negligible.zero

theorem StatisticalIndist.of_Perfect {Aux : Type u} {X Y : Ensemble Aux}
    (h : PerfectIndist X Y) :
    StatisticalIndist zeroError X Y :=
  h.statistical

theorem ComputationalIndist.of_Perfect {Aux : Type u} {X Y : Ensemble Aux}
    (h : PerfectIndist X Y) :
    ComputationalIndist X Y :=
  h.computational

end LeanCryptoProtocols.UC

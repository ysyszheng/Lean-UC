import Mathlib
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# 三层不可区分接口

本文件把执行结果看作随辅助输入 `z` 与安全参数 `n` 变化的分布族，并给出：

- 完美不可区分 `≡`
- 统计不可区分 `≈ₛ`
- 计算不可区分 `≈_c`

其中：

- `≈ₛ` 通过全变差距离定义，不依赖 distinguisher；
- `≈_c` 通过全局 `PPT` 谓词约束下的 distinguisher 定义。
-/

universe u v

namespace LeanCryptoProtocols.UC

/-- 带辅助输入与安全参数的执行 ensemble。 -/
abbrev Ensemble (Aux : Type u) (α : Type v) : Type (max u v) := Aux → ℕ → PMF α

/-- 全局的 PPT 谓词接口。后续困难性假设与安全定义统一复用它。 -/
axiom PPT : {α : Sort u} → α → Prop

/-- 计算安全层沿用 mathlib 的超多项式衰减接口。 -/
def Negligible (f : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) f

/-- 三种安全级别。 -/
inductive SecurityLevel where
  | perfect
  | statistical
  | computational
  deriving DecidableEq, Repr

/-- 输出为 `true` 的概率。 -/
noncomputable def probTrue (d : PMF Bool) : ℝ :=
  ENNReal.toReal (d true)

/-- `PMF` 在单点上的实数概率质量。 -/
noncomputable def pmfMass {α : Type v} (p : PMF α) (a : α) : ℝ :=
  ENNReal.toReal (p a)

/--
全变差距离。

当前实现针对有限输出空间；这对当前 UC 核心中的环境输出 `Bool` 已经足够。
-/
noncomputable def TVDist {α : Type v} [Fintype α] [DecidableEq α] (p q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |pmfMass p a - pmfMass q a|

/-- 统计不可区分的显式界函数版本。 -/
def StatisticalIndistBound {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    (ε : ℕ → ℝ) (X Y : Ensemble Aux α) : Prop :=
  ∀ z n, TVDist (X z n) (Y z n) ≤ ε n

/-- 完美不可区分：逐点完全相等。 -/
def PerfectIndist {Aux : Type u} {α : Type v} (X Y : Ensemble Aux α) : Prop :=
  ∀ z n, X z n = Y z n

/-- 统计不可区分：存在 negligible 上界控制全变差距离。 -/
def StatisticalIndist {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    (X Y : Ensemble Aux α) : Prop :=
  ∃ negl, Negligible negl ∧ StatisticalIndistBound negl X Y

/-- non-uniform polynomial-time distinguisher。 -/
structure Distinguisher (Aux : Type u) (α : Type v) where
  run : α → Aux → ℕ → PMF Bool

/-- distinguisher 观察 `X(z,n)` 后诱导出的 bit 输出分布。 -/
noncomputable def DistOutput {Aux : Type u} {α : Type v}
    (D : Distinguisher Aux α) (X : Ensemble Aux α) (z : Aux) (n : ℕ) : PMF Bool :=
  (X z n).bind fun x => D.run x z n

/-- distinguisher 对两个 ensemble 的区分优势。 -/
noncomputable def DistAdvantage {Aux : Type u} {α : Type v}
    (D : Distinguisher Aux α) (X Y : Ensemble Aux α) (z : Aux) (n : ℕ) : ℝ :=
  |probTrue (DistOutput D X z n) - probTrue (DistOutput D Y z n)|

/-- 计算不可区分：任意 PPT distinguisher 的优势都被某个 negligible 上界控制。 -/
def ComputationalIndist {Aux : Type u} {α : Type v} (X Y : Ensemble Aux α) : Prop :=
  ∀ D : Distinguisher Aux α, PPT D →
    ∃ negl, Negligible negl ∧ ∀ z n, DistAdvantage D X Y z n ≤ negl n

/-- 统一的三层不可区分接口。 -/
def Indistinguishable {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    (level : SecurityLevel) (X Y : Ensemble Aux α) : Prop :=
  match level with
  | .perfect => PerfectIndist X Y
  | .statistical => StatisticalIndist X Y
  | .computational => ComputationalIndist X Y

/-- 完美不可区分的数学记号。 -/
infix:50 " ≡ " => PerfectIndist

/-- 统计不可区分的数学记号。 -/
infix:50 " ≈ₛ " => StatisticalIndist

/-- 计算不可区分的数学记号。 -/
infix:50 " ≈_c " => ComputationalIndist

/-- 默认零函数。 -/
def zeroBound : ℕ → ℝ := 0

@[simp] theorem TVDist_nonneg {α : Type v} [Fintype α] [DecidableEq α] (p q : PMF α) :
    0 ≤ TVDist p q := by
  unfold TVDist
  positivity

@[simp] theorem TVDist_self {α : Type v} [Fintype α] [DecidableEq α] (p : PMF α) :
    TVDist p p = 0 := by
  classical
  unfold TVDist pmfMass
  simp

theorem TVDist_symm {α : Type v} [Fintype α] [DecidableEq α] (p q : PMF α) :
    TVDist p q = TVDist q p := by
  classical
  unfold TVDist
  congr 1
  refine Finset.sum_congr rfl ?_
  intro a _
  simp [pmfMass, abs_sub_comm]

theorem TVDist_triangle {α : Type v} [Fintype α] [DecidableEq α] (p q r : PMF α) :
    TVDist p r ≤ TVDist p q + TVDist q r := by
  classical
  unfold TVDist
  have hsum :
      ∑ a, |pmfMass p a - pmfMass r a| ≤
        ∑ a, (|pmfMass p a - pmfMass q a| + |pmfMass q a - pmfMass r a|) := by
    refine Finset.sum_le_sum ?_
    intro a _
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_sub_le (pmfMass p a) (pmfMass q a) (pmfMass r a)
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  calc
    (1 / 2 : ℝ) * ∑ a, |pmfMass p a - pmfMass r a| ≤
        (1 / 2 : ℝ) *
          ∑ a, (|pmfMass p a - pmfMass q a| + |pmfMass q a - pmfMass r a|) :=
      mul_le_mul_of_nonneg_left hsum hhalf
    _ = (1 / 2 : ℝ) * ∑ a, |pmfMass p a - pmfMass q a| +
          (1 / 2 : ℝ) * ∑ a, |pmfMass q a - pmfMass r a| := by
      rw [Finset.sum_add_distrib, mul_add]

@[simp] theorem DistAdvantage_nonneg {Aux : Type u} {α : Type v}
    (D : Distinguisher Aux α) (X Y : Ensemble Aux α) (z : Aux) (n : ℕ) :
    0 ≤ DistAdvantage D X Y z n := by
  simp [DistAdvantage]

theorem DistAdvantage_comm {Aux : Type u} {α : Type v}
    (D : Distinguisher Aux α) (X Y : Ensemble Aux α) (z : Aux) (n : ℕ) :
    DistAdvantage D X Y z n = DistAdvantage D Y X z n := by
  simp [DistAdvantage, abs_sub_comm]

theorem DistAdvantage_triangle {Aux : Type u} {α : Type v}
    (D : Distinguisher Aux α) (X Y Z : Ensemble Aux α) (z : Aux) (n : ℕ) :
    DistAdvantage D X Z z n ≤ DistAdvantage D X Y z n + DistAdvantage D Y Z z n := by
  dsimp [DistAdvantage, probTrue]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    abs_sub_le
      (ENNReal.toReal (DistOutput D X z n true))
      (ENNReal.toReal (DistOutput D Y z n true))
      (ENNReal.toReal (DistOutput D Z z n true))

theorem PerfectIndist.refl {Aux : Type u} {α : Type v}
    (X : Ensemble Aux α) : PerfectIndist X X := by
  intro z n
  rfl

theorem PerfectIndist.symm {Aux : Type u} {α : Type v} {X Y : Ensemble Aux α} :
    PerfectIndist X Y → PerfectIndist Y X := by
  intro h z n
  symm
  exact h z n

theorem PerfectIndist.trans {Aux : Type u} {α : Type v} {X Y Z : Ensemble Aux α} :
    PerfectIndist X Y → PerfectIndist Y Z → PerfectIndist X Z := by
  intro hXY hYZ z n
  rw [hXY z n, hYZ z n]

theorem StatisticalIndist.refl {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    (X : Ensemble Aux α) : StatisticalIndist X X := by
  refine ⟨zeroBound, ?_, ?_⟩
  · dsimp [Negligible, zeroBound]
    exact Asymptotics.superpolynomialDecay_zero Filter.atTop (fun n : ℕ => (n : ℝ))
  · intro z n
    simp [zeroBound]

theorem StatisticalIndist.symm {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    {X Y : Ensemble Aux α} :
    StatisticalIndist X Y → StatisticalIndist Y X := by
  rintro ⟨negl, hnegl, hbound⟩
  refine ⟨negl, hnegl, ?_⟩
  intro z n
  simpa [TVDist_symm] using hbound z n

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

theorem StatisticalIndist.trans {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    {X Y Z : Ensemble Aux α} :
    StatisticalIndist X Y → StatisticalIndist Y Z → StatisticalIndist X Z := by
  rintro ⟨negl₁, hnegl₁, h₁⟩ ⟨negl₂, hnegl₂, h₂⟩
  refine ⟨fun n => negl₁ n + negl₂ n, Negligible.add hnegl₁ hnegl₂, ?_⟩
  intro z n
  calc
    TVDist (X z n) (Z z n) ≤ TVDist (X z n) (Y z n) + TVDist (Y z n) (Z z n) :=
      TVDist_triangle (X z n) (Y z n) (Z z n)
    _ ≤ negl₁ n + negl₂ n := add_le_add (h₁ z n) (h₂ z n)

theorem PerfectIndist.statistical {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    {X Y : Ensemble Aux α} (h : PerfectIndist X Y) :
    StatisticalIndist X Y := by
  refine ⟨zeroBound, Negligible.zero, ?_⟩
  intro z n
  rw [h z n]
  simp [zeroBound]

theorem ComputationalIndist.refl {Aux : Type u} {α : Type v} (X : Ensemble Aux α) :
    ComputationalIndist X X := by
  intro D hD
  refine ⟨zeroBound, Negligible.zero, ?_⟩
  intro z n
  have hzero : DistAdvantage D X X z n = 0 := by
    simp [DistAdvantage]
  simpa [zeroBound] using le_of_eq hzero

theorem ComputationalIndist.symm {Aux : Type u} {α : Type v} {X Y : Ensemble Aux α} :
    ComputationalIndist X Y → ComputationalIndist Y X := by
  intro h D hD
  obtain ⟨negl, hnegl, hbound⟩ := h D hD
  refine ⟨negl, hnegl, ?_⟩
  intro z n
  simpa [DistAdvantage_comm] using hbound z n

theorem ComputationalIndist.trans {Aux : Type u} {α : Type v} {X Y Z : Ensemble Aux α}
    (hXY : ComputationalIndist X Y)
    (hYZ : ComputationalIndist Y Z) :
    ComputationalIndist X Z := by
  intro D hD
  obtain ⟨negl₁, hnegl₁, h₁⟩ := hXY D hD
  obtain ⟨negl₂, hnegl₂, h₂⟩ := hYZ D hD
  refine ⟨fun n => negl₁ n + negl₂ n, Negligible.add hnegl₁ hnegl₂, ?_⟩
  intro z n
  calc
    DistAdvantage D X Z z n ≤ DistAdvantage D X Y z n + DistAdvantage D Y Z z n :=
      DistAdvantage_triangle D X Y Z z n
    _ ≤ negl₁ n + negl₂ n := add_le_add (h₁ z n) (h₂ z n)

theorem PerfectIndist.computational {Aux : Type u} {α : Type v}
    {X Y : Ensemble Aux α} (h : PerfectIndist X Y) :
    ComputationalIndist X Y := by
  intro D hD
  refine ⟨zeroBound, Negligible.zero, ?_⟩
  intro z n
  have hzero : DistAdvantage D X Y z n = 0 := by
    simp [DistAdvantage, DistOutput, h z n]
  simpa [zeroBound] using le_of_eq hzero

theorem StatisticalIndist.of_Perfect {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α]
    {X Y : Ensemble Aux α} (h : PerfectIndist X Y) :
    StatisticalIndist X Y :=
  h.statistical

theorem ComputationalIndist.of_Perfect {Aux : Type u} {α : Type v}
    {X Y : Ensemble Aux α} (h : PerfectIndist X Y) :
    ComputationalIndist X Y :=
  h.computational

example {Aux : Type u} {α : Type v} (X : Ensemble Aux α) : X ≡ X :=
  PerfectIndist.refl X

example {Aux : Type u} {α : Type v} [Fintype α] [DecidableEq α] (X : Ensemble Aux α) : X ≈ₛ X :=
  StatisticalIndist.refl X

example {Aux : Type u} {α : Type v} (X : Ensemble Aux α) : X ≈_c X :=
  ComputationalIndist.refl X

end LeanCryptoProtocols.UC

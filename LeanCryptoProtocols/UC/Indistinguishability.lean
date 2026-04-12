import Mathlib
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# 三层不可区分接口

本文件把执行结果看作只随安全参数 `n` 变化的分布族，并给出：

- 完美不可区分 `≡`
- 统计不可区分 `≈ₛ`
- 计算不可区分 `≈_c`

其中：

- `≈ₛ` 通过全变差距离定义，不依赖 distinguisher；
- `≈_c` 通过全局 `PPT` 谓词约束下的 uniform distinguisher 定义。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- 只依赖安全参数 `n` 的执行 ensemble。 -/
abbrev Ensemble (α : Type u) : Type u := ℕ → PMF α

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
noncomputable def pmfMass {α : Type u} (p : PMF α) (a : α) : ℝ :=
  ENNReal.toReal (p a)

/--
全变差距离。

当前实现针对有限输出空间；这对当前 UC 核心中的环境输出 `Bool` 已经足够。
-/
noncomputable def TVDist {α : Type u} [Fintype α] [DecidableEq α] (p q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |pmfMass p a - pmfMass q a|

/-- 统计不可区分的显式界函数版本。 -/
def StatisticalIndistBound {α : Type u} [Fintype α] [DecidableEq α]
    (ε : ℕ → ℝ) (X Y : Ensemble α) : Prop :=
  ∀ n, TVDist (X n) (Y n) ≤ ε n

/-- 完美不可区分：逐点完全相等。 -/
def PerfectIndist {α : Type u} (X Y : Ensemble α) : Prop :=
  ∀ n, X n = Y n

/-- 统计不可区分：存在 negligible 上界控制全变差距离。 -/
def StatisticalIndist {α : Type u} [Fintype α] [DecidableEq α]
    (X Y : Ensemble α) : Prop :=
  ∃ negl, Negligible negl ∧ StatisticalIndistBound negl X Y

/-- uniform polynomial-time distinguisher。 -/
structure Distinguisher (α : Type u) where
  run : α → ℕ → PMF Bool

/-- distinguisher 观察 `X n` 后诱导出的 bit 输出分布。 -/
noncomputable def DistOutput {α : Type u}
    (D : Distinguisher α) (X : Ensemble α) (n : ℕ) : PMF Bool :=
  (X n).bind fun x => D.run x n

/-- distinguisher 对两个 ensemble 的区分优势。 -/
noncomputable def DistAdvantage {α : Type u}
    (D : Distinguisher α) (X Y : Ensemble α) (n : ℕ) : ℝ :=
  |probTrue (DistOutput D X n) - probTrue (DistOutput D Y n)|

/-- 计算不可区分：任意 PPT distinguisher 的优势都被某个 negligible 上界控制。 -/
def ComputationalIndist {α : Type u} (X Y : Ensemble α) : Prop :=
  ∀ D : Distinguisher α, PPT D →
    ∃ negl, Negligible negl ∧ ∀ n, DistAdvantage D X Y n ≤ negl n

/-- 统一的三层不可区分接口。 -/
def Indistinguishable {α : Type u} [Fintype α] [DecidableEq α]
    (level : SecurityLevel) (X Y : Ensemble α) : Prop :=
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

/-- `Bool` 上的恒等 distinguisher。 -/
noncomputable def boolIdentityDistinguisher : Distinguisher Bool where
  run b _ := PMF.pure b

/-- 假设：`Bool` 恒等 distinguisher 是 PPT。 -/
axiom PPT_boolIdentityDistinguisher : PPT boolIdentityDistinguisher

@[simp] theorem TVDist_nonneg {α : Type u} [Fintype α] [DecidableEq α] (p q : PMF α) :
    0 ≤ TVDist p q := by
  unfold TVDist
  positivity

@[simp] theorem TVDist_self {α : Type u} [Fintype α] [DecidableEq α] (p : PMF α) :
    TVDist p p = 0 := by
  classical
  unfold TVDist pmfMass
  simp

theorem TVDist_symm {α : Type u} [Fintype α] [DecidableEq α] (p q : PMF α) :
    TVDist p q = TVDist q p := by
  classical
  unfold TVDist
  congr 1
  refine Finset.sum_congr rfl ?_
  intro a _
  simp [pmfMass, abs_sub_comm]

theorem TVDist_triangle {α : Type u} [Fintype α] [DecidableEq α] (p q r : PMF α) :
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

@[simp] theorem DistAdvantage_nonneg {α : Type u}
    (D : Distinguisher α) (X Y : Ensemble α) (n : ℕ) :
    0 ≤ DistAdvantage D X Y n := by
  simp [DistAdvantage]

theorem DistAdvantage_comm {α : Type u}
    (D : Distinguisher α) (X Y : Ensemble α) (n : ℕ) :
    DistAdvantage D X Y n = DistAdvantage D Y X n := by
  simp [DistAdvantage, abs_sub_comm]

theorem DistAdvantage_triangle {α : Type u}
    (D : Distinguisher α) (X Y Z : Ensemble α) (n : ℕ) :
    DistAdvantage D X Z n ≤ DistAdvantage D X Y n + DistAdvantage D Y Z n := by
  dsimp [DistAdvantage, probTrue]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    abs_sub_le
      (ENNReal.toReal (DistOutput D X n true))
      (ENNReal.toReal (DistOutput D Y n true))
      (ENNReal.toReal (DistOutput D Z n true))

theorem PerfectIndist.refl {α : Type u}
    (X : Ensemble α) : PerfectIndist X X := by
  intro n
  rfl

theorem PerfectIndist.symm {α : Type u} {X Y : Ensemble α} :
    PerfectIndist X Y → PerfectIndist Y X := by
  intro h n
  symm
  exact h n

theorem PerfectIndist.trans {α : Type u} {X Y Z : Ensemble α} :
    PerfectIndist X Y → PerfectIndist Y Z → PerfectIndist X Z := by
  intro hXY hYZ n
  rw [hXY n, hYZ n]

theorem StatisticalIndist.refl {α : Type u} [Fintype α] [DecidableEq α]
    (X : Ensemble α) : StatisticalIndist X X := by
  refine ⟨zeroBound, ?_, ?_⟩
  · dsimp [Negligible, zeroBound]
    exact Asymptotics.superpolynomialDecay_zero Filter.atTop (fun n : ℕ => (n : ℝ))
  · intro n
    simp [zeroBound]

theorem StatisticalIndist.symm {α : Type u} [Fintype α] [DecidableEq α]
    {X Y : Ensemble α} :
    StatisticalIndist X Y → StatisticalIndist Y X := by
  rintro ⟨negl, hnegl, hbound⟩
  refine ⟨negl, hnegl, ?_⟩
  intro n
  simpa [TVDist_symm] using hbound n

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

/-- `Bool` 分布上，`false` 和 `true` 的概率质量之和为 `1`。 -/
theorem pmfMass_false_add_true (p : PMF Bool) :
    pmfMass p false + pmfMass p true = 1 := by
  have hsum : p false + p true = 1 := by
    simpa [Fintype.sum_bool, add_comm] using (PMF.tsum_coe p)
  exact ENNReal.toReal_add (p.apply_ne_top false) (p.apply_ne_top true) ▸ by
    simpa [pmfMass] using congrArg ENNReal.toReal hsum

/-- `Bool` 分布上，`false` 的概率质量可由 `true` 的概率质量恢复。 -/
theorem pmfMass_false_eq_one_sub_true (p : PMF Bool) :
    pmfMass p false = 1 - pmfMass p true := by
  linarith [pmfMass_false_add_true p]

theorem StatisticalIndist.trans {α : Type u} [Fintype α] [DecidableEq α]
    {X Y Z : Ensemble α} :
    StatisticalIndist X Y → StatisticalIndist Y Z → StatisticalIndist X Z := by
  rintro ⟨negl₁, hnegl₁, h₁⟩ ⟨negl₂, hnegl₂, h₂⟩
  refine ⟨fun n => negl₁ n + negl₂ n, Negligible.add hnegl₁ hnegl₂, ?_⟩
  intro n
  calc
    TVDist (X n) (Z n) ≤ TVDist (X n) (Y n) + TVDist (Y n) (Z n) :=
      TVDist_triangle (X n) (Y n) (Z n)
    _ ≤ negl₁ n + negl₂ n := add_le_add (h₁ n) (h₂ n)

theorem PerfectIndist.statistical {α : Type u} [Fintype α] [DecidableEq α]
    {X Y : Ensemble α} (h : PerfectIndist X Y) :
    StatisticalIndist X Y := by
  refine ⟨zeroBound, Negligible.zero, ?_⟩
  intro n
  rw [h n]
  simp [zeroBound]

theorem ComputationalIndist.refl {α : Type u} (X : Ensemble α) :
    ComputationalIndist X X := by
  intro D hD
  refine ⟨zeroBound, Negligible.zero, ?_⟩
  intro n
  have hzero : DistAdvantage D X X n = 0 := by
    simp [DistAdvantage]
  simpa [zeroBound] using le_of_eq hzero

theorem ComputationalIndist.symm {α : Type u} {X Y : Ensemble α} :
    ComputationalIndist X Y → ComputationalIndist Y X := by
  intro h D hD
  obtain ⟨negl, hnegl, hbound⟩ := h D hD
  refine ⟨negl, hnegl, ?_⟩
  intro n
  simpa [DistAdvantage_comm] using hbound n

theorem ComputationalIndist.trans {α : Type u} {X Y Z : Ensemble α}
    (hXY : ComputationalIndist X Y)
    (hYZ : ComputationalIndist Y Z) :
    ComputationalIndist X Z := by
  intro D hD
  obtain ⟨negl₁, hnegl₁, h₁⟩ := hXY D hD
  obtain ⟨negl₂, hnegl₂, h₂⟩ := hYZ D hD
  refine ⟨fun n => negl₁ n + negl₂ n, Negligible.add hnegl₁ hnegl₂, ?_⟩
  intro n
  calc
    DistAdvantage D X Z n ≤ DistAdvantage D X Y n + DistAdvantage D Y Z n :=
      DistAdvantage_triangle D X Y Z n
    _ ≤ negl₁ n + negl₂ n := add_le_add (h₁ n) (h₂ n)

theorem PerfectIndist.computational {α : Type u}
    {X Y : Ensemble α} (h : PerfectIndist X Y) :
    ComputationalIndist X Y := by
  intro D hD
  refine ⟨zeroBound, Negligible.zero, ?_⟩
  intro n
  have hzero : DistAdvantage D X Y n = 0 := by
    simp [DistAdvantage, DistOutput, h n]
  simpa [zeroBound] using le_of_eq hzero

theorem StatisticalIndist.of_Perfect {α : Type u} [Fintype α] [DecidableEq α]
    {X Y : Ensemble α} (h : PerfectIndist X Y) :
    StatisticalIndist X Y :=
  h.statistical

theorem ComputationalIndist.of_Perfect {α : Type u}
    {X Y : Ensemble α} (h : PerfectIndist X Y) :
    ComputationalIndist X Y :=
  h.computational

/-- 完美不可区分的 `Bool` 特化：输出 `true` 的概率完全相等。 -/
theorem PerfectIndist.probTrue_eq {X Y : Ensemble Bool}
    (h : PerfectIndist X Y) :
    ∀ n, probTrue (X n) = probTrue (Y n) := by
  intro n
  rw [h n]

/-- 统计不可区分的 `Bool` 特化：`true` 事件的概率差被 negligible 控制。 -/
theorem StatisticalIndist.probTrue_bound {X Y : Ensemble Bool}
    (h : StatisticalIndist X Y) :
    ∃ negl, Negligible negl ∧ ∀ n, |probTrue (X n) - probTrue (Y n)| ≤ negl n := by
  rcases h with ⟨negl, hnegl, hbound⟩
  refine ⟨negl, hnegl, ?_⟩
  intro n
  have htv :
      (1 / 2 : ℝ) *
          (|pmfMass (X n) false - pmfMass (Y n) false| +
            |pmfMass (X n) true - pmfMass (Y n) true|) ≤ negl n := by
    simpa [TVDist, Fintype.sum_bool, add_comm] using hbound n
  have hfalse :
      pmfMass (X n) false - pmfMass (Y n) false =
        -(pmfMass (X n) true - pmfMass (Y n) true) := by
    rw [pmfMass_false_eq_one_sub_true, pmfMass_false_eq_one_sub_true]
    ring
  have habs :
      |pmfMass (X n) false - pmfMass (Y n) false| =
        |pmfMass (X n) true - pmfMass (Y n) true| := by
    rw [hfalse, abs_neg]
  have hhalf :
      (1 / 2 : ℝ) *
          (|pmfMass (X n) true - pmfMass (Y n) true| +
            |pmfMass (X n) true - pmfMass (Y n) true|) =
        |pmfMass (X n) true - pmfMass (Y n) true| := by
    ring
  calc
    |probTrue (X n) - probTrue (Y n)| =
        |pmfMass (X n) true - pmfMass (Y n) true| := by
      rfl
    _ = (1 / 2 : ℝ) *
          (|pmfMass (X n) false - pmfMass (Y n) false| +
            |pmfMass (X n) true - pmfMass (Y n) true|) := by
      rw [habs]
      symm
      exact hhalf
    _ ≤ negl n := htv

/--
计算不可区分的 `Bool` 特化：
使用恒等 distinguisher 得到 `true` 事件的概率差被 negligible 控制。
-/
theorem ComputationalIndist.identity_bound {X Y : Ensemble Bool}
    (h : ComputationalIndist X Y) :
    ∃ negl, Negligible negl ∧ ∀ n, |probTrue (X n) - probTrue (Y n)| ≤ negl n := by
  rcases h boolIdentityDistinguisher PPT_boolIdentityDistinguisher with ⟨negl, hnegl, hbound⟩
  refine ⟨negl, hnegl, ?_⟩
  intro n
  simpa [DistAdvantage, DistOutput, boolIdentityDistinguisher, probTrue]
    using hbound n

example {α : Type u} (X : Ensemble α) : X ≡ X :=
  PerfectIndist.refl X

example {α : Type u} [Fintype α] [DecidableEq α] (X : Ensemble α) : X ≈ₛ X :=
  StatisticalIndist.refl X

example {α : Type u} (X : Ensemble α) : X ≈_c X :=
  ComputationalIndist.refl X

end LeanCryptoProtocols.UC

import Mathlib

/-!
# 严格分布型 UC 核心接口

本文件将先前的 UC MVP 升级为严格的 real / ideal 分布型安全定义。

当前版本仍然保留第一阶段的建模边界：

- 两方协议；
- 静态腐化；
- 半诚实敌手；
- 同步 transcript / local-view 语义；
- 用 `PMF` 建模随机执行。

与之前的 `support` 风格定义不同，这里显式引入：

- 观察分布；
- 环境区分优势；
- `∀ adv, ∃ sim, ∀ env` 的 UC 风格量词顺序；
- 完美 / 统计 / 计算三层不可区分接口。
-/

namespace LeanCryptoProtocols.UC

open scoped BigOperators

universe u v w x

/-- 两方协议中的参与方编号。 -/
abbrev PartyId : Type := Fin 2

/-- 左侧参与方。 -/
def left : PartyId := ⟨0, by decide⟩

/-- 右侧参与方。 -/
def right : PartyId := ⟨1, by decide⟩

@[simp] theorem left_ne_right : left ≠ right := by
  decide

@[simp] theorem right_ne_left : right ≠ left := by
  decide

/-- 静态腐化集合。 -/
abbrev Corruption : Type := PartyId → Prop

/-- 当前核心层只考虑半诚实、静态腐化模型。 -/
class StaticSemiHonest : Prop where

instance : StaticSemiHonest := ⟨⟩

/-- 四种标准腐化情形。 -/
inductive CorruptionCase where
  | none
  | left
  | right
  | both
  deriving DecidableEq, Repr

/-- 将枚举形式的腐化情形转成谓词。 -/
def caseToCorruption : CorruptionCase → Corruption
  | .none => fun _ => False
  | .left => fun p => p = left
  | .right => fun p => p = right
  | .both => fun _ => True

/-- 从腐化谓词恢复为四种标准情形之一。 -/
noncomputable def corruptionCase (corr : Corruption) : CorruptionCase := by
  classical
  by_cases hLeft : corr left
  · by_cases hRight : corr right
    · exact .both
    · exact .left
  · by_cases hRight : corr right
    · exact .right
    · exact .none

theorem caseToCorruption_corruptionCase (corr : Corruption) :
    caseToCorruption (corruptionCase corr) = corr := by
  classical
  funext p
  fin_cases p
  · simp [corruptionCase, caseToCorruption, left, right]
    split_ifs <;> simp_all
  · simp [corruptionCase, caseToCorruption, left, right]
    split_ifs <;> simp_all

@[simp] theorem corruptionCase_none :
    corruptionCase (caseToCorruption .none) = .none := by
  simp [corruptionCase, caseToCorruption]

@[simp] theorem corruptionCase_left :
    corruptionCase (caseToCorruption .left) = .left := by
  simp [corruptionCase, caseToCorruption]

@[simp] theorem corruptionCase_right :
    corruptionCase (caseToCorruption .right) = .right := by
  simp [corruptionCase, caseToCorruption]

@[simp] theorem corruptionCase_both :
    corruptionCase (caseToCorruption .both) = .both := by
  simp [corruptionCase, caseToCorruption]

/-- transcript 的最小封装。 -/
structure Transcript (Event : Type u) where
  events : List Event
  deriving Repr, DecidableEq

/-- 某个执行中每个参与方的本地视图。 -/
abbrev LocalView (View : Type u) : Type u := PartyId → View

/-- 敌手可见的腐化视图。 -/
abbrev ObservedView (View : Type u) : Type u := PartyId → Option View

/-- 随安全参数变化的分布族。 -/
abbrev DistFamily (α : Type u) : Type u := ℕ → PMF α

/-- 协议执行在本地视图上的分布族。 -/
abbrev ExecDist (View : Type u) : Type u := DistFamily (LocalView View)

/-- 环境在观察分布上输出一个 bit。 -/
structure Environment (View : Type u) where
  run : ObservedView View → Bool

/-- 真实协议接口。 -/
abbrev Protocol (Adv : Type u) (Input : Type v) (View : Type w) : Type (max u v w) :=
  Corruption → Adv → Input → ExecDist View

/-- 固定敌手后选出的模拟器接口。 -/
abbrev Simulator (Input : Type u) (Output : Type v) (View : Type w) :
    Type (max u v w) :=
  Corruption → Input → Output → ExecDist View

/-- 将单个分布视为常值分布族。 -/
def constFamily {α : Type u} (d : PMF α) : DistFamily α :=
  fun _ => d

/-- 只保留被腐化方可见的视图。 -/
noncomputable def observedView {View : Type u} (corr : Corruption)
    (view : LocalView View) : ObservedView View := by
  classical
  exact fun p => if corr p then some (view p) else none

/-- 将执行分布投影到被腐化方可见的观察分布。 -/
noncomputable def ObservedDist {View : Type u} (corr : Corruption) (exec : ExecDist View) :
    DistFamily (ObservedView View) :=
  fun n => PMF.map (observedView corr) (exec n)

/-- 真实世界的观察分布。 -/
noncomputable def RealModel {Adv : Type u} {Input : Type v} {View : Type w}
    (protocol : Protocol Adv Input View) (corr : Corruption) (adv : Adv) (input : Input) :
    DistFamily (ObservedView View) :=
  ObservedDist corr (protocol corr adv input)

/-- 理想世界的观察分布。 -/
noncomputable def IdealModel {Input : Type u} {Output : Type v} {View : Type w}
    (idealOut : Input → Output)
    (sim : Simulator Input Output View)
    (corr : Corruption) (input : Input) :
    DistFamily (ObservedView View) :=
  ObservedDist corr (sim corr input (idealOut input))

/-- 环境在某个安全参数下输出 `true` 的概率。 -/
noncomputable def envProb {View : Type u} (env : Environment View)
    (dist : PMF (ObservedView View)) : ℝ :=
  (PMF.map env.run dist true).toReal

/-- 环境对两个观察分布的区分优势。 -/
noncomputable def Advantage {View : Type u} (env : Environment View)
    (real ideal : DistFamily (ObservedView View)) : ℕ → ℝ :=
  fun n => |envProb env (real n) - envProb env (ideal n)|

/-- 计算安全层使用的“可忽略函数”接口。 -/
def Negligible (f : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) f

/-- 三种安全级别。 -/
inductive SecurityLevel where
  | perfect
  | statistical
  | computational
  deriving DecidableEq, Repr

/-- 完美不可区分：两个观察分布族逐点完全相等。 -/
def PerfectIndist {View : Type u}
    (real ideal : DistFamily (ObservedView View)) : Prop :=
  ∀ n, real n = ideal n

/-- 统计不可区分：对固定环境，区分优势由 `ε` 上界。 -/
def StatisticalIndist {View : Type u} (ε : ℕ → ℝ)
    (env : Environment View)
    (real ideal : DistFamily (ObservedView View)) : Prop :=
  ∀ n, Advantage env real ideal n ≤ ε n

/-- 计算不可区分：对 PPT 环境，区分优势可忽略。 -/
def ComputationalIndist {View : Type u}
    (PPTEnv : Environment View → Prop)
    (env : Environment View)
    (real ideal : DistFamily (ObservedView View)) : Prop :=
  PPTEnv env → Negligible (Advantage env real ideal)

/-- 统一的不可区分接口。 -/
def Indistinguishable {View : Type u}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTEnv : Environment View → Prop)
    (env : Environment View)
    (real ideal : DistFamily (ObservedView View)) : Prop :=
  match level with
  | .perfect => PerfectIndist real ideal
  | .statistical => StatisticalIndist ε env real ideal
  | .computational => ComputationalIndist PPTEnv env real ideal

/-- 默认的零误差函数。 -/
def zeroError : ℕ → ℝ := fun _ => 0

/--
严格的 UC 风格安全定义：
- TODO: check
- 对任意敌手 `adv`；
- 存在模拟器 `sim`；
- 对任意环境 `env`、腐化集合 `corr` 和输入 `input`；
- real / ideal 两个观察分布族在给定安全级别下不可区分。
-/
def UCSecureAt
    {Adv : Type u} {Input : Type v} {Output : Type w} {View : Type x}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTEnv : Environment View → Prop)
    (realProtocol : Protocol Adv Input View)
    (idealOut : Input → Output) : Prop :=
  ∀ adv, ∃ sim : Simulator Input Output View, ∀ env corr input,
    Indistinguishable level ε PPTEnv env
      (RealModel realProtocol corr adv input)
      (IdealModel idealOut sim corr input)

/-- 完美安全层的简写。 -/
def UCSecure
    {Adv : Type u} {Input : Type v} {Output : Type w} {View : Type x}
    (realProtocol : Protocol Adv Input View)
    (idealOut : Input → Output) : Prop :=
  UCSecureAt .perfect zeroError (fun _ => True) realProtocol idealOut

@[simp] theorem observedView_none {View : Type u} (view : LocalView View) :
    observedView (caseToCorruption .none) view = fun _ => none := by
  funext p
  simp [observedView, caseToCorruption]

theorem observedView_left_of_eq {View : Type u} {v₁ v₂ : LocalView View}
    (h : v₁ left = v₂ left) :
    observedView (caseToCorruption .left) v₁ =
      observedView (caseToCorruption .left) v₂ := by
  funext p
  fin_cases p
  · simpa [observedView, caseToCorruption, left] using congrArg some h
  · simp [observedView, caseToCorruption, left]

theorem observedView_right_of_eq {View : Type u} {v₁ v₂ : LocalView View}
    (h : v₁ right = v₂ right) :
    observedView (caseToCorruption .right) v₁ =
      observedView (caseToCorruption .right) v₂ := by
  funext p
  fin_cases p
  · simp [observedView, caseToCorruption, right]
  · simpa [observedView, caseToCorruption, right] using congrArg some h

theorem observedView_both_of_eq {View : Type u} {v₁ v₂ : LocalView View}
    (hLeft : v₁ left = v₂ left) (hRight : v₁ right = v₂ right) :
    observedView (caseToCorruption .both) v₁ =
      observedView (caseToCorruption .both) v₂ := by
  funext p
  fin_cases p
  · simpa [observedView, caseToCorruption, left] using congrArg some hLeft
  · simpa [observedView, caseToCorruption, right] using congrArg some hRight

/-- 完美不可区分推出任意环境在每个安全参数下的输出概率相同。 -/
theorem PerfectIndist.envProb_eq
    {View : Type u}
    {real ideal : DistFamily (ObservedView View)}
    (h : PerfectIndist real ideal)
    (env : Environment View) (n : ℕ) :
    envProb env (real n) = envProb env (ideal n) := by
  simp [h n]

/--
若已经为每个敌手固定了一个统一模拟器族，并分别证明四种腐化情形下的不可区分，
则可合成为通用的 `UCSecureAt` 结论。
-/
theorem UCSecureAt.of_cases
    {Adv : Type u} {Input : Type v} {Output : Type w} {View : Type x}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTEnv : Environment View → Prop)
    (realProtocol : Protocol Adv Input View)
    (idealOut : Input → Output)
    (simulatorFor : ∀ _ : Adv, Simulator Input Output View)
    (hNone :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel realProtocol (caseToCorruption .none) adv input)
          (IdealModel idealOut (simulatorFor adv) (caseToCorruption .none) input))
    (hLeft :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel realProtocol (caseToCorruption .left) adv input)
          (IdealModel idealOut (simulatorFor adv) (caseToCorruption .left) input))
    (hRight :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel realProtocol (caseToCorruption .right) adv input)
          (IdealModel idealOut (simulatorFor adv) (caseToCorruption .right) input))
    (hBoth :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel realProtocol (caseToCorruption .both) adv input)
          (IdealModel idealOut (simulatorFor adv) (caseToCorruption .both) input)) :
    UCSecureAt level ε PPTEnv realProtocol idealOut := by
  unfold UCSecureAt
  intro adv
  refine ⟨simulatorFor adv, ?_⟩
  intro env corr input
  have hc : caseToCorruption (corruptionCase corr) = corr :=
    caseToCorruption_corruptionCase corr
  cases hCase : corruptionCase corr
  · have hcorr : corr = caseToCorruption .none := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hNone adv env input
  · have hcorr : corr = caseToCorruption .left := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hLeft adv env input
  · have hcorr : corr = caseToCorruption .right := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hRight adv env input
  · have hcorr : corr = caseToCorruption .both := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hBoth adv env input

end LeanCryptoProtocols.UC

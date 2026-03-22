import Mathlib

/-!
# UC MVP 核心接口

本文件给出一个适用于当前项目第一阶段的最小 UC 风格证明内核。

设计目标：

- 仅支持两方协议；
- 仅建模静态腐化、半诚实敌手；
- 使用 transcript / local view 语义，而不是完整异步调度；
- 安全性采用“可观察视图的 support 相等”这一完美安全风格定义；
- 为后续扩展到统计距离 / 计算不可区分保留接口形状。
-/

namespace LeanCryptoProtocols.UC

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

/-- 当前 MVP 只考虑半诚实、静态腐化模型。 -/
class StaticSemiHonest : Prop where

instance : StaticSemiHonest := ⟨⟩

/-- 四种腐化情形。 -/
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

-- forall adv, exists sim, forall env, view env real approx view env ideal

/-- transcript 的最小封装。 -/
structure Transcript (Event : Type u) where
  events : List Event
  deriving Repr, DecidableEq

/-- 某个执行中每个参与方的本地视图。 -/
abbrev LocalView (View : Type u) : Type u := PartyId → View

/-- 通用交互机接口；后续可以替换为更复杂的执行语义。 -/
structure InteractiveMachine (State : Type u) (Input : Type v) (Output : Type w)
    (Event : Type x) where
  init : State
  step : State → Input → State × Output × Event

/-- 理想功能的最小接口。 -/
structure IdealFunctionality (Input : Type u) (Output : Type v) (Event : Type w) where
  run : Input → Output × Transcript Event

/-- 环境在当前 MVP 中只观察被腐化方视图。 -/
structure Environment (View : Type u) where
  distinguish : (PartyId → Option View) → Bool

/-- 敌手接口在第一版中保持抽象。 -/
structure Adversary (View : Type u) where
  observe : LocalView View → LocalView View

/-- 模拟器以理想输出为输入，生成模拟视图。 -/
structure Simulator (Input : Type u) (Output : Type v) (Seed : Type w) (View : Type x) where
  run : Corruption → Input → Output → Seed → LocalView View

/-- 只保留被腐化方可见的视图。 -/
noncomputable def observedView {View : Type u} (corr : Corruption)
    (view : LocalView View) : PartyId → Option View := by
  classical
  exact fun p => if corr p then some (view p) else none

/-- 在给定输入上的真实执行。 -/
def RealExec {Input : Type u} {Seed : Type v} {View : Type w}
    (protocol : Input → Seed → LocalView View) (input : Input) : Seed → LocalView View :=
  protocol input

/-- 在给定输入与理想输出上的模拟执行。 -/
def IdealExec {Input : Type u} {Output : Type v} {Seed : Type w} {View : Type x}
    (idealOut : Input → Output)
    (sim : Corruption → Input → Output → Seed → LocalView View)
    (corr : Corruption) (input : Input) : Seed → LocalView View :=
  sim corr input (idealOut input)

/-- 被腐化方可观察视图的 support。 -/
def Support {Seed : Type u} {View : Type v}
    (corr : Corruption) (exec : Seed → LocalView View) :
    Set (PartyId → Option View) :=
  { obs | ∃ seed, observedView corr (exec seed) = obs }

-- TODO: 后续替换为严格的UC安全的定义
/-- 完美模拟：真实世界与理想世界的可观察 support 完全一致。 -/
def PerfectSimulates {SeedR : Type u} {SeedI : Type v} {View : Type w}
    (corr : Corruption)
    (realExec : SeedR → LocalView View)
    (idealExec : SeedI → LocalView View) : Prop :=
  Support corr realExec = Support corr idealExec

/-- 当前 MVP 中的 UC 风格安全定义。 -/
def UCSecureMVP
    {Input : Type u} {Output : Type v} {SeedR : Type w} {SeedI : Type x}
    {View : Type u}
    (realProtocol : Input → SeedR → LocalView View)
    (idealOut : Input → Output)
    (sim : Corruption → Input → Output → SeedI → LocalView View) : Prop :=
  ∀ corr input,
    PerfectSimulates corr (RealExec realProtocol input) (IdealExec idealOut sim corr input)

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

/--
按四种腐化情形分别证明后，可以合成为通用的 `UCSecureMVP` 结论。
-/
theorem UCSecureMVP.of_cases
    {Input : Type u} {Output : Type v} {SeedR : Type w} {SeedI : Type x}
    {View : Type u}
    (realProtocol : Input → SeedR → LocalView View)
    (idealOut : Input → Output)
    (sim : Corruption → Input → Output → SeedI → LocalView View)
    (hNone :
      ∀ input,
        PerfectSimulates (caseToCorruption .none)
          (RealExec realProtocol input)
          (IdealExec idealOut sim (caseToCorruption .none) input))
    (hLeft :
      ∀ input,
        PerfectSimulates (caseToCorruption .left)
          (RealExec realProtocol input)
          (IdealExec idealOut sim (caseToCorruption .left) input))
    (hRight :
      ∀ input,
        PerfectSimulates (caseToCorruption .right)
          (RealExec realProtocol input)
          (IdealExec idealOut sim (caseToCorruption .right) input))
    (hBoth :
      ∀ input,
        PerfectSimulates (caseToCorruption .both)
          (RealExec realProtocol input)
          (IdealExec idealOut sim (caseToCorruption .both) input)) :
    UCSecureMVP realProtocol idealOut sim := by
  intro corr input
  have hc : caseToCorruption (corruptionCase corr) = corr :=
    caseToCorruption_corruptionCase corr
  cases hCase : corruptionCase corr
  · have hcorr : corr = caseToCorruption .none := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hNone input
  · have hcorr : corr = caseToCorruption .left := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hLeft input
  · have hcorr : corr = caseToCorruption .right := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hRight input
  · have hcorr : corr = caseToCorruption .both := by
      simpa [hCase] using hc.symm
    subst corr
    simpa using hBoth input

end LeanCryptoProtocols.UC

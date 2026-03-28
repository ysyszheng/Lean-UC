import Mathlib

/-!
# 同步轮次下的严格 UC 核心接口

本文件给出当前项目采用的严格 UC 风格核心接口，范围固定为：

- 两方协议；
- 静态腐化；
- 半诚实敌手；
- 同步固定轮次；
- 用分布族描述 real / ideal 视图；
- 安全定义写成 `∀ adv, ∃ sim, ∀ env`。

当前最关键的约束是：`Simulator` 只接收被腐化方输入、被腐化方输出以及理想功能允许泄漏的信息，
而不再直接接收完整协议输入。
-/

universe u v w x

namespace LeanCryptoProtocols.UC

open scoped BigOperators

/-- 两方协议中的参与方编号。 -/
abbrev PartyId : Type := Fin 2

/-- 左方。 -/
def left : PartyId := ⟨0, by decide⟩

/-- 右方。 -/
def right : PartyId := ⟨1, by decide⟩

@[simp] theorem left_ne_right : left ≠ right := by
  decide

@[simp] theorem right_ne_left : right ≠ left := by
  decide

/-- 当前框架只处理静态腐化下的四种标准情形。 -/
inductive CorruptionCase where
  | none
  | left
  | right
  | both
  deriving DecidableEq, Repr

/-- 判断某参与方在给定腐化情形下是否被腐化。 -/
def CorruptionCase.contains : CorruptionCase → PartyId → Prop
  | .none, _ => False
  | .left, p => p = LeanCryptoProtocols.UC.left
  | .right, p => p = LeanCryptoProtocols.UC.right
  | .both, _ => True

/-- 当前核心层默认的敌手模型：静态、半诚实。 -/
class StaticSemiHonest : Prop where

instance : StaticSemiHonest := ⟨⟩

/-- 协议中的定向消息。 -/
structure Packet (Msg : Type u) where
  src : PartyId
  dst : PartyId
  payload : Msg
  deriving Repr, DecidableEq

/-- 本地机可观察到的单步事件。 -/
inductive LocalEvent (Msg : Type u) where
  | recv : Packet Msg → LocalEvent Msg
  | send : Packet Msg → LocalEvent Msg
  deriving Repr, DecidableEq

/--
事件驱动本地机。

这里不强迫所有协议都通过统一执行器运行，但协议建模应当能清楚地落到这个接口上：
收到一条消息，更新本地状态，并发出若干消息。
-/
structure ProtocolMachine
    (State : Type u) (Input : Type v) (Coins : Type w)
    (Msg : Type x) (Output : Type u) where
  init : Input → Coins → State
  onReceive : State → Packet Msg → State × List (Packet Msg)
  finish : State → Output

/-- 某个执行中每个参与方的本地视图。 -/
abbrev LocalView (View : Type u) : Type u := PartyId → View

/-- 环境真正能看到的、只保留腐化方的视图。 -/
abbrev ObservedView (View : Type u) : Type u := PartyId → Option View

/-- 随安全参数变化的分布族。 -/
abbrev DistFamily (α : Type u) : Type u := ℕ → PMF α

/-- 执行分布族：每个安全参数给出一个本地视图分布。 -/
abbrev ExecDist (View : Type u) : Type u := DistFamily (LocalView View)

/-- 环境读取被腐化方观察视图并输出一个 bit。 -/
structure Environment (View : Type u) where
  run : ObservedView View → Bool

/-- 理想世界允许 simulator 访问的信息接口。 -/
structure IdealInterface (Input : Type u) (Output : Type v) where
  CorruptedInput : CorruptionCase → Type u
  CorruptedOutput : CorruptionCase → Type v
  Leakage : CorruptionCase → Type (max u v)
  corruptInput : (corr : CorruptionCase) → Input → CorruptedInput corr
  corruptOutput : (corr : CorruptionCase) → Output → CorruptedOutput corr
  leakage : (corr : CorruptionCase) → Input → Output → Leakage corr

/-- 理想功能：真实输入映射到理想输出，并显式给出 simulator 可见接口。 -/
structure IdealFunctionality (Input : Type u) (Output : Type v) where
  eval : Input → Output
  interface : IdealInterface Input Output

/-- 真实世界协议：给定腐化情形、敌手与输入，产生视图分布族。 -/
abbrev Protocol (Adv : Type u) (Input : Type v) (View : Type w) :
    Type (max u v w) :=
  CorruptionCase → Adv → Input → ExecDist View

/-- 模拟器：只接收被腐化方输入、输出与理想泄漏。 -/
abbrev Simulator {Input : Type u} {Output : Type v}
    (I : IdealInterface Input Output) (View : Type w) :
    Type (max u v w) :=
  (corr : CorruptionCase) →
    I.CorruptedInput corr →
    I.CorruptedOutput corr →
    I.Leakage corr →
    ExecDist View

/-- 将单个分布视为常值分布族。 -/
def constFamily {α : Type u} (d : PMF α) : DistFamily α :=
  fun _ => d

/-- 从本地视图中裁剪出环境能见到的腐化方视图。 -/
noncomputable def observedView {View : Type u}
    (corr : CorruptionCase) (view : LocalView View) : ObservedView View :=
  match corr with
  | .none => fun _ => none
  | .left =>
      fun p =>
        if p = left then some (view p) else none
  | .right =>
      fun p =>
        if p = right then some (view p) else none
  | .both => fun p => some (view p)

/-- 将执行分布投影为环境可见的观察分布。 -/
noncomputable def ObservedDist {View : Type u}
    (corr : CorruptionCase) (exec : ExecDist View) : DistFamily (ObservedView View) :=
  fun n => PMF.map (observedView corr) (exec n)

/-- 真实世界观察分布。 -/
noncomputable def RealModel {Adv : Type u} {Input : Type v} {View : Type w}
    (protocol : Protocol Adv Input View)
    (corr : CorruptionCase) (adv : Adv) (input : Input) :
    DistFamily (ObservedView View) :=
  ObservedDist corr (protocol corr adv input)

/-- 理想世界观察分布。 -/
noncomputable def IdealModel {Input : Type u} {Output : Type v} {View : Type w}
    (ideal : IdealFunctionality Input Output)
    (sim : Simulator ideal.interface View)
    (corr : CorruptionCase) (input : Input) :
    DistFamily (ObservedView View) :=
  let out := ideal.eval input
  let cin := ideal.interface.corruptInput corr input
  let cout := ideal.interface.corruptOutput corr out
  let leak := ideal.interface.leakage corr input out
  ObservedDist corr (sim corr cin cout leak)

/-- 环境在某个安全参数下输出 `true` 的概率。 -/
noncomputable def envProb {View : Type u}
    (env : Environment View) (dist : PMF (ObservedView View)) : ℝ :=
  ENNReal.toReal (∑' ov, if env.run ov then dist ov else 0)

/-- 环境区分真实 / 理想观察分布的优势。 -/
noncomputable def Advantage {View : Type u}
    (env : Environment View)
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

/-- 完美不可区分：观察分布族逐点相等。 -/
def PerfectIndist {View : Type u}
    (real ideal : DistFamily (ObservedView View)) : Prop :=
  ∀ n, real n = ideal n

/-- 统计不可区分：对固定环境，优势被误差函数上界。 -/
def StatisticalIndist {View : Type u}
    (ε : ℕ → ℝ)
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

- `∀ adv`
- `∃ sim`
- `∀ env`
- 对任意腐化情形与输入，real / ideal 的观察分布在给定安全级别下不可区分。
-/
def UCSecureAt {Adv : Type u} {Input : Type v} {Output : Type w} {View : Type x}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTEnv : Environment View → Prop)
    (protocol : Protocol Adv Input View)
    (ideal : IdealFunctionality Input Output) : Prop :=
  ∀ adv, ∃ sim : Simulator ideal.interface View, ∀ env corr input,
    Indistinguishable level ε PPTEnv env
      (RealModel protocol corr adv input)
      (IdealModel ideal sim corr input)

/-- 完美安全层的专用简写。 -/
def UCSecurePerfect {Adv : Type u} {Input : Type v} {Output : Type w} {View : Type x}
    (protocol : Protocol Adv Input View)
    (ideal : IdealFunctionality Input Output) : Prop :=
  UCSecureAt .perfect zeroError (fun _ => True) protocol ideal

/-- 向后兼容的别名。 -/
abbrev UCSecure := @UCSecurePerfect

@[simp] theorem observedView_none {View : Type u} (view : LocalView View) :
    observedView .none view = (fun _ => none) := by
  funext p
  simp [observedView]

theorem observedView_left_of_eq {View : Type u} {v₁ v₂ : LocalView View}
    (h : v₁ left = v₂ left) :
    observedView .left v₁ = observedView .left v₂ := by
  funext p
  fin_cases p
  · simpa [observedView, left] using congrArg some h
  · simp [observedView, left]

theorem observedView_right_of_eq {View : Type u} {v₁ v₂ : LocalView View}
    (h : v₁ right = v₂ right) :
    observedView .right v₁ = observedView .right v₂ := by
  funext p
  fin_cases p
  · simp [observedView, right]
  · simpa [observedView, right] using congrArg some h

theorem observedView_both_of_eq {View : Type u} {v₁ v₂ : LocalView View}
    (hLeft : v₁ left = v₂ left) (hRight : v₁ right = v₂ right) :
    observedView .both v₁ = observedView .both v₂ := by
  funext p
  fin_cases p
  · simpa [observedView, left] using congrArg some hLeft
  · simpa [observedView, right] using congrArg some hRight

/-- 完美不可区分推出任意环境的输出概率相同。 -/
theorem PerfectIndist.envProb_eq
    {View : Type u}
    {real ideal : DistFamily (ObservedView View)}
    (h : PerfectIndist real ideal)
    (env : Environment View) (n : ℕ) :
    envProb env (real n) = envProb env (ideal n) := by
  simp [envProb, h n]

/--
按四种腐化情形分别证明后，可合成为总 UC 安全定理。
-/
theorem UCSecureAt.of_cases {Adv : Type u} {Input : Type v} {Output : Type w} {View : Type x}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTEnv : Environment View → Prop)
    (protocol : Protocol Adv Input View)
    (ideal : IdealFunctionality Input Output)
    (simulatorFor : Adv → Simulator ideal.interface View)
    (hNone :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel protocol .none adv input)
          (IdealModel ideal (simulatorFor adv) .none input))
    (hLeft :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel protocol .left adv input)
          (IdealModel ideal (simulatorFor adv) .left input))
    (hRight :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel protocol .right adv input)
          (IdealModel ideal (simulatorFor adv) .right input))
    (hBoth :
      ∀ adv env input,
        Indistinguishable level ε PPTEnv env
          (RealModel protocol .both adv input)
          (IdealModel ideal (simulatorFor adv) .both input)) :
    UCSecureAt level ε PPTEnv protocol ideal := by
  intro adv
  refine ⟨simulatorFor adv, ?_⟩
  intro env corr input
  cases corr with
  | none => simpa using hNone adv env input
  | left => simpa using hLeft adv env input
  | right => simpa using hRight adv env input
  | both => simpa using hBoth adv env input

end LeanCryptoProtocols.UC

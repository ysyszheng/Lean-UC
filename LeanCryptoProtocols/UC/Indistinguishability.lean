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

/--
全局的 PPT 谓词接口。

当前仓库把“多项式时间”作为抽象复杂度层处理：这里不在 Lean 中展开具体的
成本语义或机模型，而是提供一个统一的 `PPT` 谓词，供：

- 敌手；
- simulator；
- distinguisher；
- reduction；
- 困难性假设中的采样器/生成器

共同复用。

除 `PPT` 及其闭包性质外，本项目的 computational 安全主线不再依赖其他
“隐藏 proof 的 axiom”。
-/
axiom PPT : {α : Sort u} → α → Prop

/-- judgmental 相等下的 `PPT` 保持性。 -/
axiom ppt_congr {α : Sort u} {x y : α} :
  x = y → PPT x → PPT y

/-- 确定性函数复合保持 `PPT`。 -/
axiom ppt_comp {α β γ : Sort u}
    {f : α → β} {g : β → γ} :
    PPT f → PPT g → PPT (fun x => g (f x))

/-- 常值算法是 `PPT`。 -/
axiom ppt_const {α β : Sort u} (b : β) :
  PPT (fun _ : α => b)

/-- 概率纯返回是 `PPT`。 -/
axiom ppt_pure {α : Sort u} {β : Type u} (f : α → β) :
  PPT f → PPT (fun x => PMF.pure (f x))

/--
随机化算法的顺序组合保持 `PPT`。

这里把 `α → PMF β` 看作一次随机化过程；若前置算法是 `PPT`，且后处理对每个输入
都给出 `PPT` 算法，则整体仍是 `PPT`。
-/
axiom ppt_bind {α : Sort u} {β γ : Type u}
    {f : α → PMF β} {g : β → PMF γ} :
    PPT f → (∀ b, PPT (g b)) → PPT (fun x => (f x).bind g)

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

end LeanCryptoProtocols.UC

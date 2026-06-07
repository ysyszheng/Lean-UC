import LeanCryptoProtocols.UC.Indistinguishability

/-!
# DDH 假设

本文件记录后续归约使用的标准 DDH 假设接口。

群生成算法接收安全参数 `n` 并采样一个群描述。
DDH 真实分布采样 `a,b` 并输出
`(g^a, g^b, g^(ab))`；随机分布采样 `a,b,c` 并输出 `(g^a, g^b, g^c)`。
-/

universe u

namespace LeanCryptoProtocols.Assumptions

open LeanCryptoProtocols.UC

/--
用于密码学游戏的抽象群描述。

`Exponent` 是游戏中采样的指数表示；
`mul_exp` 是构造 `ab` 时使用的指数运算。
具体群实例如果在归约中需要循环群定律，应在实例侧额外提供这些性质。
-/
structure GroupDescription where
  Element : Type u
  Exponent : Type u
  generator : Element
  pow : Element → Exponent → Element
  encode : Element → Nat
  mul_exp : Exponent → Exponent → Exponent
  sample_exponent : PMF Exponent

/-- 由安全参数索引的群生成算法。 -/
abbrev GroupGenerator : Type (u + 1) :=
  ℕ → PMF (GroupDescription.{u})

/-- DDH 类假设中使用的 PPT 群生成算法。 -/
structure PPTGroupGenerator where
  run : GroupGenerator.{u}
  ppt : PPT run

/-- 在一个采样出的群描述上的 DDH 挑战。 -/
structure DDHChallenge (G : GroupDescription.{u}) where
  gx : G.Element
  gy : G.Element
  gz : G.Element

/-- DDH 游戏样本用依赖对隐藏被生成的具体群。 -/
abbrev DDHSample : Type (u + 1) :=
  Σ G : GroupDescription.{u}, DDHChallenge G

/-- DDH 真实分布：`(g^a, g^b, g^(ab))`。 -/
noncomputable def ddh_real (gen : GroupGenerator.{u}) : Ensemble DDHSample :=
  fun n =>
    (gen n).bind fun G =>
      G.sample_exponent.bind fun a =>
        G.sample_exponent.bind fun b =>
          PMF.pure
            ⟨G,
              { gx := G.pow G.generator a
                gy := G.pow G.generator b
                gz := G.pow G.generator (G.mul_exp a b) }⟩

/-- DDH 随机分布：`(g^a, g^b, g^c)`。 -/
noncomputable def ddh_random (gen : GroupGenerator.{u}) : Ensemble DDHSample :=
  fun n =>
    (gen n).bind fun G =>
      G.sample_exponent.bind fun a =>
        G.sample_exponent.bind fun b =>
          G.sample_exponent.bind fun c =>
            PMF.pure
              ⟨G,
                { gx := G.pow G.generator a
                  gy := G.pow G.generator b
                  gz := G.pow G.generator c }⟩

/-- 区分器针对 DDH 游戏的优势。 -/
noncomputable def ddh_advantage (gen : GroupGenerator.{u})
    (D : Distinguisher DDHSample) (n : ℕ) : ℝ :=
  DistAdvantage D (ddh_real gen) (ddh_random gen) n

/--
针对一个群生成算法的标准计算型 DDH 假设。

对任意 PPT 区分器，真实 DDH 挑战分布族和随机 DDH 挑战分布族
作为安全参数 `n` 的函数是计算不可区分的。
-/
def ddh_assumption (gen : GroupGenerator.{u}) : Prop :=
  ComputationalIndist (ddh_real gen) (ddh_random gen)

/-- 与 PPT 群生成算法打包在一起的 DDH 假设。 -/
def ppt_ddh_assumption (gen : PPTGroupGenerator.{u}) : Prop :=
  ddh_assumption gen.run

end LeanCryptoProtocols.Assumptions

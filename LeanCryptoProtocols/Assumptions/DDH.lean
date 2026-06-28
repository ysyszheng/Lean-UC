import LeanCryptoProtocols.UC.Indistinguishability

/-!
# DDH 假设

本文件记录后续归约使用的固定群 DDH 假设接口。

群、生成元和群运算在整个实验中固定；安全参数 `n` 只索引
ensemble。DDH 真实分布采样 `a,b` 并输出
`(g^a, g^b, g^(ab))`；随机分布采样 `a,b,c` 并输出 `(g^a, g^b, g^c)`。
-/

universe u

namespace LeanCryptoProtocols.Assumptions

open LeanCryptoProtocols.UC

/--
用于密码学游戏的固定抽象群环境。

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
  decode : Nat → Option Element
  mul_exp : Exponent → Exponent → Exponent
  sample_exponent : PMF Exponent
  decode_encode : ∀ x : Element, decode (encode x) = some x
  pow_mul_generator :
    ∀ a b : Exponent,
      pow (pow generator a) b = pow generator (mul_exp a b)
  pow_mul_generator_comm :
    ∀ a b : Exponent,
      pow (pow generator a) b = pow (pow generator b) a

/-- 在固定群环境上的 DDH 挑战。 -/
structure DDHChallenge (G : GroupDescription.{u}) where
  gx : G.Element
  gy : G.Element
  gz : G.Element

/-- DDH 真实分布：`(g^a, g^b, g^(ab))`。 -/
noncomputable def ddh_real (G : GroupDescription.{u}) : Ensemble (DDHChallenge G) :=
  fun _ =>
    G.sample_exponent.bind fun a =>
      G.sample_exponent.bind fun b =>
        PMF.pure
          { gx := G.pow G.generator a
            gy := G.pow G.generator b
            gz := G.pow G.generator (G.mul_exp a b) }

/-- DDH 随机分布：`(g^a, g^b, g^c)`。 -/
noncomputable def ddh_random (G : GroupDescription.{u}) : Ensemble (DDHChallenge G) :=
  fun _ =>
    G.sample_exponent.bind fun a =>
      G.sample_exponent.bind fun b =>
        G.sample_exponent.bind fun c =>
          PMF.pure
            { gx := G.pow G.generator a
              gy := G.pow G.generator b
              gz := G.pow G.generator c }

/-- 区分器针对 DDH 游戏的优势。 -/
noncomputable def ddh_advantage (G : GroupDescription.{u})
    (D : Distinguisher (DDHChallenge G)) (n : ℕ) : ℝ :=
  DistAdvantage D (ddh_real G) (ddh_random G) n

/--
针对固定群环境的标准计算型 DDH 假设。

对任意 PPT 区分器，真实 DDH 挑战分布族和随机 DDH 挑战分布族
作为安全参数 `n` 的函数是计算不可区分的。
-/
def ddh_assumption (G : GroupDescription.{u}) : Prop :=
  ComputationalIndist (ddh_real G) (ddh_random G)

end LeanCryptoProtocols.Assumptions

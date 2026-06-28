import LeanCryptoProtocols.Assumptions.DDH
import LeanCryptoProtocols.UC.Functionality.SMCCommon

set_option linter.flexible false

/-!
# SMC EasyUC 中的固定群 DH 公共组件

本文件只封装真实 DHKE machines 共用的局部计算。
群环境 `G` 在整个协议中固定；每次会话只采样新的指数。
-/

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC

open LeanCryptoProtocols.Assumptions
open LeanCryptoProtocols.UC.Functionality

/-- 固定群 `G` 中一方的 DH 局部 secret。 -/
structure DHSecret (G : GroupDescription.{0}) where
  exponent : G.Exponent
  public_share : GroupElement

/-- 在固定群 `G` 中采样指数 `a` 并生成 `g^a`。 -/
noncomputable def sample_dh_secret
    (G : GroupDescription.{0}) : PMF (DHSecret G) :=
  G.sample_exponent.bind fun a =>
    PMF.pure {
      exponent := a
      public_share := ⟨G.encode (G.pow G.generator a)⟩
    }

/-- 用本地指数和对方公开 share 计算 DH key。 -/
def derive_key_from_secret {G : GroupDescription.{0}}
    (secret : DHSecret G) (peer_share : GroupElement) : SharedKey :=
  match G.decode peer_share.value with
  | some peer_element =>
      ⟨G.encode (G.pow peer_element secret.exponent)⟩
  | none =>
      default_shared_key

/-- 在 `G` 中持有 `a` 的一方从 `g^b` 导出 `g^(ab)`。 -/
theorem derive_key_from_secret_generator
    (G : GroupDescription.{0}) (a b : G.Exponent) :
    derive_key_from_secret
        { exponent := a
          public_share := ⟨G.encode (G.pow G.generator a)⟩ }
        ⟨G.encode (G.pow G.generator b)⟩ =
      ⟨G.encode (G.pow G.generator (G.mul_exp a b))⟩ := by
  simp [derive_key_from_secret, G.decode_encode]
  rw [← G.pow_mul_generator_comm a b, G.pow_mul_generator]

/-- 固定群中双方从对方 share 导出同一个 DH key。 -/
theorem derive_key_from_secret_comm
    (G : GroupDescription.{0}) (a b : G.Exponent) :
    derive_key_from_secret
        { exponent := a
          public_share := ⟨G.encode (G.pow G.generator a)⟩ }
        ⟨G.encode (G.pow G.generator b)⟩ =
      derive_key_from_secret
        { exponent := b
          public_share := ⟨G.encode (G.pow G.generator b)⟩ }
        ⟨G.encode (G.pow G.generator a)⟩ := by
  simp [derive_key_from_secret, G.decode_encode]
  exact congrArg G.encode (G.pow_mul_generator_comm a b).symm

end LeanCryptoProtocols.CaseStudy.SMCEasyUC

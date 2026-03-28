import LeanCryptoProtocols.GMW.OTHybrid.Model
import LeanCryptoProtocols.GMW.OTHybrid.Security
import LeanCryptoProtocols.UC.Functionality.OT
import LeanCryptoProtocols.UC.Functionality.SFE

/-!
# GMW OT-hybrid UC 证明证书

本文件是审核入口。审核者应当优先检查这里，而不是先读详细证明文件。

本证书重复完整陈述以下最小单元：

1. 证明所在的 world；
2. 协议的建模入口；
3. 目标理想功能；
4. 最终 UC 定理。

详细的 simulator 构造与证明脚本位于 `Security.lean`。
-/

namespace LeanCryptoProtocols.GMW.OTHybrid.Certificate

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Circuit
open LeanCryptoProtocols.GMW.OTHybrid

/-! ## World -/

/-- GMW 证书中使用的参与方类型。 -/
abbrev GMWPartyId := PartyId

/-- GMW 证书中固定的腐化模型：静态半诚实。 -/
abbrev GMWCorruptionModel : Prop := StaticSemiHonest

/-- GMW 证书中固定的安全级别：完美安全。 -/
abbrev GMWSecurityLevel : SecurityLevel := .perfect

/-- GMW 所处 hybrid world 中使用的 OT 理想功能。 -/
def GMWHybridOT : IdealFunctionality OTInput OTOutput := IdealOT

/-! ## Protocol -/

/-- GMW 协议的输入类型。 -/
abbrev GMWInput (c : BoolCircuit) := Inputs c

/-- GMW 协议给环境暴露的本地视图类型。 -/
abbrev GMWView := PartyView

/--
GMW 在 OT-hybrid world 中的真实协议入口。

审核者需要核对：

- XOR 门免费；
- NOT 门本地处理；
- 每个 AND 门通过两个 `1-out-of-2 OT` 调用 `IdealOT`。
-/
noncomputable def GMWRealProtocol {Adv : Type} (c : BoolCircuit) :
    Protocol Adv (Inputs c) PartyView :=
  realProtocol (Adv := Adv) c

/-! ## Ideal Functionality -/

/-- GMW 要实现的目标理想功能。 -/
def GMWTargetIdealF (c : BoolCircuit) : IdealFunctionality (Inputs c) Bool :=
  IdealBoolCircuitSFE c

/-! ## UC Theorem -/

/--
GMW 在 OT-hybrid world 下的严格 UC 定理。

这里直接以 `UCSecureAt` 的完整形状重述最终结论，便于审核者单独检查。
-/
theorem gmw_ot_hybrid_uc_certificate {Adv : Type} (c : BoolCircuit) :
    UCSecureAt .perfect zeroError (fun _ => True)
      (GMWRealProtocol (Adv := Adv) c)
      (GMWTargetIdealF c) := by
  simpa [GMWRealProtocol, GMWTargetIdealF] using
    (gmw_ot_hybrid_uc_secure_perfect (Adv := Adv) c)

/-- GMW 在 OT-hybrid world 下的完美 UC 安全便捷表述。 -/
theorem gmw_ot_hybrid_uc_certificate_perfect {Adv : Type} (c : BoolCircuit) :
    UCSecurePerfect
      (GMWRealProtocol (Adv := Adv) c)
      (GMWTargetIdealF c) := by
  simpa [GMWRealProtocol, GMWTargetIdealF] using
    (gmw_ot_hybrid_uc_secure_perfect (Adv := Adv) c)

end LeanCryptoProtocols.GMW.OTHybrid.Certificate

import LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE.Certificate.CertificateProofs
import LeanCryptoProtocols.UC.Security

/-!
# DHKE 子证明的审计证书入口

本文件只暴露审计者需要确认的对象：

- 真实 DH key exchange protocol；
- 理想 KE functionality；
- 以 UC-realize 表述的安全目标。
-/

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Assumptions

/-- DHKE 子证明的 UC-realize 目标陈述。 -/
def uc_realizes
    (G : GroupDescription.{0}) : Prop :=
  ddh_assumption G →
    UCRealizesComputational
      (real_protocol G)
      (ideal_ke_functionality G)

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

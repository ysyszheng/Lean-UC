import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.CertificateProofs
import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Model
import LeanCryptoProtocols.UC.Security

/-!
# SMC EasyUC case study 的审计证书入口

本文件只暴露审计者需要定位的核心对象：

- real SMC protocol；
- SMC 理想功能；
- UC-realize 安全目标陈述。

具体的协议程序与端口定义见 `Certificate.CertificateObjects`；
well-formed 与 protocol-shape 证明见 `Certificate.CertificateProofs`。
-/

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC

universe wA wE

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Assumptions

/-- Certificate 中的 UC 安全目标陈述。证明将在后续安全证明文件中完成。 -/
def smc_uc_realizes
    (G : GroupDescription.{0}) : Prop :=
  ddh_assumption G →
    UCRealizesComputational
      (real_smc_protocol G)
      ideal_smc_functionality

/--
固定 simulator 版本的 SMC UC 安全目标陈述。

这里不再证明 `∃ S`；理想世界 adversary 固定为 `smc_simulator A`。
该目标目前只是审计入口中的 theorem statement，完整证明将在后续文件中完成。
-/
def smc_uc_realizes_with_fixed_simulator
    (G : GroupDescription.{0}) : Prop :=
  ddh_assumption G →
    ∀ A : Adversary.{0, wA} SMCEasyUCPayload, PPT A →
      ∀ E : Environment.{0, wE} SMCEasyUCPayload, PPT E →
        ∀ real_setup : ExecutionSetup (real_smc_protocol G) A E,
          ∀ ideal_setup :
              ExecutionSetup
                (mk_ideal_protocol ideal_smc_functionality).protocol
                (smc_simulator A)
                E,
            ∃ negl, Negligible negl ∧
              ∀ n, exec_diff real_setup ideal_setup n ≤ negl n

end LeanCryptoProtocols.CaseStudy.SMCEasyUC

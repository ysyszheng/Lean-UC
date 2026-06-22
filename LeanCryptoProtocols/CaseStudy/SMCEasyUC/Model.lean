import LeanCryptoProtocols.UC.Security
import LeanCryptoProtocols.UC.Functionality.SMCCommon

/-!
# SMC EasyUC case study 的 SMC-level 模型入口

DHKE 子证明已移动到 `SMCEasyUC.DHKE`。本文件只保留 SMC 层后续证明
需要引用的固定 simulator 构造接口。
-/

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality

/--
固定的 secure-message simulator 构造接口。

最终 UC 目标使用固定的 `S(A)`，而不是再证明 `∃ S`。完整程序将在后续
SMC-level 证明中细化；DH key exchange 子步骤的 simulator 已在
`SMCEasyUC.DHKE.Model` 中单独实现。
-/
def smc_simulator (A : Adversary SMCEasyUCPayload) :
    Simulator SMCEasyUCPayload :=
  A

end LeanCryptoProtocols.CaseStudy.SMCEasyUC

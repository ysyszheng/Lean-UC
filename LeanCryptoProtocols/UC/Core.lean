import LeanCryptoProtocols.UC.Machine
import LeanCryptoProtocols.UC.Indistinguishability
import LeanCryptoProtocols.UC.Security
import LeanCryptoProtocols.UC.Composition
import LeanCryptoProtocols.UC.Channel

/-!
# Canetti Section 2 风格的 UC 核心入口

本文件只做聚合导出。新的 UC 框架分为五层：

- `Machine`：machine / communication set / protocol shape
- `Indistinguishability`：完美 / 统计 / 计算不可区分
- `Security`：UC-emulate / ideal protocol / UC-realize
- `Composition`：compatible / identity-compatible / universal composition
- `Channel`：authenticated communication 的 channel machine

当前主框架固定为：

- `n` 方；
- static corruption；
- semi-honest；
- authenticated communication；
- 以 Canetti 2000 第 2 节的简化模型为蓝本。
-/


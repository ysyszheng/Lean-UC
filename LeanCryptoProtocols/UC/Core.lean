import LeanCryptoProtocols.UC.Machine
import LeanCryptoProtocols.UC.Indistinguishability
import LeanCryptoProtocols.UC.Security
import LeanCryptoProtocols.UC.Composition

/-!
# Canetti Section 2 风格的 UC 核心入口

本文件只做聚合导出。新的 UC 框架分为四层：

- `Machine`：machine / communication set / protocol 静态结构
- `Indistinguishability`：完美 / 统计 / 计算不可区分
- `Security`：UC-emulate / ideal protocol / UC-realize
- `Composition`：基于执行约化的 universal composition

当前主框架固定为：

- active adversary；
- 由 `ExecutionSetup` 固定的 static corruption pattern；
- 通过显式 communication ports 与 controller 路由刻画通信；
- uniform：只保留安全参数 `n`，不建模额外辅助输入；
- 以 Canetti 2000 第 2 节的简化模型为蓝本。
-/

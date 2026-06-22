# lean-crypto-protocols

这是一个用 Lean 形式化隐私计算协议安全证明的实验项目。

当前主线已经切换为按 Canetti 2000 第 2 节重建 UC 框架，而不是继续沿用旧的
“直接返回 view 分布”的协议接口。

## 当前主框架

当前框架固定在以下边界：

- `n` 方协议
- static corruption
- semi-honest 敌手
- 同步加密授权通信
- uniform：只保留安全参数 `n`
- 完美 / 统计 / 计算 三层不可区分
- 当前主线先聚焦 machine / controller / security / ideal functionality

## 模块结构

### 1. Machine / Protocol Shape

文件：

- `LeanCryptoProtocols/UC/Machine.lean`

提供：

- `MachineId`
- `PortLabel`
- `CommPort`
- `Envelope`
- `ActivationResult`
- `MachineProgram`
- `Machine`
- `ProtocolShape`
- caller / subroutine / subsidiary 关系
- `external identity`
- `main machine`
- `internal machine`
- `Message`
- `Envelope`

这一层只描述协议的静态结构，不直接给出 UC 安全定义。

其中 identity 现在直接使用 Canetti 风格的普通自然数：

- `MachineId = Nat`
- `envId = 0`
- `advId = 1`

并且 caller / subroutine 关系由 communication set 推出，而不是由 identity 前缀编码推出。
这些关系在 `ProtocolShape` 层只对协议内部的 machine identities 定义。
另外，`main machine` / `internal machine` 的定义按原文通过 `external identity` 给出。

其中 `PortLabel` 严格只有 Canetti 原文中的三类标准标签：

- `input`
- `subroutineOutput`
- `backdoor`

并且 `MachineProgram` 现在遵守 Section 2 的原子语义：

- 一次激活至多发送一条消息
- 不发送消息时用 `Option.none` 表示挂起

同时通信对象已经拆成两层：

- `Message`：只记录 `source` / `label` / `payload`
- `Envelope`：记录发往哪个 `CommPort`，并要求 `CommPort.label` 与 `Message.label` 一致

### 2. Indistinguishability

文件：

- `LeanCryptoProtocols/UC/Indistinguishability.lean`

提供：

- `PerfectIndist`
- `StatisticalIndist`
- `ComputationalIndist`
- `TVDist`
- `PPT`
- `Negligible`
- `DistAdvantage`

以及基础闭包引理，例如：

- 传递性
- `Perfect → Statistical`
- `Perfect → Computational`
- `Negligible.add`
- `Negligible.const_mul`

并提供数学记号：

- `X ≡ Y`
- `X ≈ₛ Y`
- `X ≈_c Y`

其中：

- `≈ₛ` 通过全变差距离定义
- `≈_c` 通过全局 `PPT` 谓词约束下的 uniform distinguisher 定义
- `Ensemble α = ℕ → PMF α`
- `Distinguisher α` 不再接收额外辅助输入

### 3. Controller

文件：

- `LeanCryptoProtocols/UC/Controller.lean`

提供：

- `Environment`
- `Adversary`
- `Simulator`
- `ExecutionSetup`
- `Controller.exec`

这里把依赖 `protocol + adversary + environment` 才能判断的执行期约束集中起来，
并由 controller 给出 uniform execution ensemble。

### 4. Security

文件：

- `LeanCryptoProtocols/UC/Security.lean`

提供：

- `IdealFunctionality`
- `DummyParty`
- `IdealProtocol`
- `mk_dummy_party`
- `mk_dummy_parties`
- `mk_ideal_protocol`
- `UCEmulatesAt`
- `UCRealizesAt`

其中：

- `IdealFunctionality` 只是一个理想功能 machine
- `IdealProtocol` 是由 dummy parties 与 ideal functionality 组成的协议
- `UCRealizesAt` 现在 realize 的对象是 `IdealFunctionality`
- ideal world 的 protocol 由 `mk_ideal_protocol` 从理想功能自动生成
- `UCEmulatesAt` 在三层上的量词顺序分别是：
  - 完美层：`∀ adversary, ∃ simulator, ∀ environment, ∀ n`
  - 统计层：`∀ adversary, ∃ simulator, ∀ environment, ∃ negl, ∀ n`
  - 计算层：`∀ PPT adversary, ∃ PPT simulator, ∀ PPT environment, ∃ negl, ∀ n`

### 5. OT Ideal Functionality

文件：

- `LeanCryptoProtocols/UC/Functionality/OT.lean`

提供：

- `F_OT`
- `OTBody`
- `OTPayload`
- `OTIds`
- `IdealOT`

其中 `IdealOT` 已经切到新的 ideal-functionality 接口：它不再走旧的
`eval/interface` 风格，而是直接返回一个 `IdealFunctionality OTPayload`。

## 其他现有模块

布尔电路组件仍然保留：

- `LeanCryptoProtocols/Circuit/BoolCircuit.lean`
- `LeanCryptoProtocols/Circuit/Examples.lean`

旧的 GMW / OT-hybrid 代码目前保留在仓库中作为过渡参考，但已经不再是当前主框架的一部分；
后续会在新的 machine / protocol / composition 语义上重写。

## 如何构建

在项目根目录执行：

```bash
cd lean-crypto-protocols
lake build
```

如果只想单独检查新的 UC 框架入口：

```bash
lake build LeanCryptoProtocols.UC.Controller
lake build LeanCryptoProtocols.UC.Security
lake build LeanCryptoProtocols.UC.Functionality.OT
```

## 当前限制

当前仍未覆盖：

- Canetti 后续章节中的更完整异步调度模型
- adaptive corruption
- malicious adversary
- `Composition.lean` 还没有按新的 controller 主线同步重构
- 在新框架上重写 GMW / OT / GC 等协议实例

这些是后续阶段的工作。



已把 `Audit.lean` 移到：

[Certificate/Audit.lean](/Users/yusen/Local/Auto-Crypto/lean-crypto-protocols/LeanCryptoProtocols/CaseStudy/SMCEasyUC/Certificate/Audit.lean:1)

新模块已验证通过：

```bash
lake build LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.Audit
```

打印审计报告有两种方式。

命令行方式，在 `lean-crypto-protocols` 根目录执行：

```bash
printf 'import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.Audit
#eval IO.println LeanCryptoProtocols.CaseStudy.SMCEasyUC.certificate_static_report
' > /tmp/smc_static_audit.lean
lake env lean /tmp/smc_static_audit.lean
```

动态 trace：

```bash
printf 'import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.Audit
#eval IO.println LeanCryptoProtocols.CaseStudy.SMCEasyUC.certificate_passive_trace
' > /tmp/smc_trace_audit.lean
lake env lean /tmp/smc_trace_audit.lean
```

VS Code 也可以。新建一个临时 `.lean` 文件，写：

```lean
import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.Audit

#eval IO.println LeanCryptoProtocols.CaseStudy.SMCEasyUC.certificate_static_report
#eval IO.println LeanCryptoProtocols.CaseStudy.SMCEasyUC.certificate_passive_trace
```

Lean 插件会在 infoview / messages 里显示输出。命令行更适合长报告，因为复制和保存更方便。
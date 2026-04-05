# lean-crypto-protocols

这是一个用 Lean 形式化隐私计算协议安全证明的实验项目。

当前主线已经切换为按 Canetti 2000 第 2 节重建 UC 框架，而不是继续沿用旧的
“直接返回 view 分布”的协议接口。

## 当前主框架

当前框架固定在以下边界：

- `n` 方协议
- static corruption
- semi-honest 敌手
- authenticated communication
- 完美 / 统计 / 计算 三层不可区分
- universal composition theorem

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
- caller / subroutine 的 identity 关系

这一层只描述协议的静态结构，不直接给出 UC 安全定义。

其中 `PortLabel` 严格只有 Canetti 原文中的三类标准标签：

- `input`
- `subroutineOutput`
- `backdoor`

并且 `MachineProgram` 现在遵守 Section 2 的原子语义：

- 一次激活至多发送一条消息
- 不发送消息时用 `Option.none` 表示挂起

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
- `≈_c` 通过全局 `PPT` 谓词约束下的 distinguisher 定义

### 3. Security

文件：

- `LeanCryptoProtocols/UC/Security.lean`

提供：

- `Environment`
- `Adversary`
- `Simulator`
- `ExecutableProtocol`
- `IdealFunctionality`
- `IdealProtocol`
- `UCEmulatesAt`
- `UCRealizesAt`

其中 `UCEmulatesAt` 的形状是标准的：

`∀ adversary, ∃ simulator, ∀ environment, indistinguishable`

### 4. Composition

文件：

- `LeanCryptoProtocols/UC/Composition.lean`

提供：

- `SubroutineProtocol`
- `Compatible`
- `IdentityCompatible`
- `ReplaceSubroutine`
- `CompositionContext`
- `CompositionSound`
- `universalComposition`

`universalComposition` 是当前框架中的主定理：如果一个 subroutine protocol
UC-emulate 它的理想版本，那么在满足 compatible / identity-compatible
以及组合语义约化条件时，把它替换进任意宿主协议后，整体协议仍保持相同安全级别的 UC-emulation。

### 5. Authenticated Communication

文件：

- `LeanCryptoProtocols/UC/Channel.lean`

提供最小的 authenticated communication `channel machine` 组件。

这个 channel machine 不再依赖额外端口标签，而是：

- 统一从 channel 自己的 `input` 端口接收消息
- 统一从 channel 自己的 `subroutineOutput` 端口发出转发消息
- 用 payload 中携带的接收者 identity 做路由

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
lake build LeanCryptoProtocols.UC.Core
```

## 当前限制

当前仍未覆盖：

- Canetti 后续章节中的更完整异步调度模型
- adaptive corruption
- malicious adversary
- 在新框架上重写 GMW / OT / GC 等协议实例

这些是后续阶段的工作。

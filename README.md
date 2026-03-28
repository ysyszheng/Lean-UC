# lean-crypto-protocols

这是一个用 Lean 形式化隐私计算协议安全证明的实验项目。当前目标不是一次性覆盖完整 UC 机器模型，而是先做一个可复用、可审计的最小核心：

- 两方协议
- 静态腐化
- 半诚实敌手
- 同步固定轮次
- 完美 / 统计 / 计算三层不可区分接口
- 优先支持 OT-hybrid 世界中的协议证明

## 当前已实现内容

### 1. UC 核心接口

文件：

- `LeanCryptoProtocols/UC/Core.lean`

提供了：

- `CorruptionCase`
- `ProtocolMachine`
- `IdealInterface`
- `IdealFunctionality`
- `Protocol`
- `Simulator`
- `ObservedDist`
- `PerfectIndist`
- `StatisticalIndist`
- `ComputationalIndist`
- `UCSecureAt`
- `UCSecurePerfect`

其中严格 UC 定义写成：

`∀ adv, ∃ sim, ∀ env, indistinguishable (...)`

并且 simulator 的输入被严格裁剪为：

- 被腐化方输入
- 被腐化方输出
- 理想功能允许泄漏的信息

不会直接拿到诚实方输入或真实执行随机性。

### 2. OT 理想功能

文件：

- `LeanCryptoProtocols/UC/Functionality/OT.lean`

当前提供 bit 级的 1-out-of-2 OT 理想功能 `F_OT`，并显式建模：

- sender 输入
- receiver 选择位
- 返回值
- sender / receiver 局部事件接口

这部分被 GMW 的 AND 门子协议直接调用。

### 3. DAG 布尔电路组件

文件：

- `LeanCryptoProtocols/Circuit/BoolCircuit.lean`
- `LeanCryptoProtocols/Circuit/Examples.lean`

电路使用“按拓扑顺序追加节点”的方式表示 DAG，因此：

- 共享子表达式天然可表示
- 无环性由类型保证
- 当前支持 `xor`、`and`、`not`

示例包括：

- 单个 XOR 门
- 单个 AND 门
- 单个 NOT 门
- 含共享子图的 DAG
- 一个混合小电路

### 4. OT-hybrid 世界中的 GMW

文件：

- `LeanCryptoProtocols/GMW/OTHybrid.lean`

当前已证明：

- `gmw_xor_gate_correct`
- `gmw_not_gate_correct`
- `gmw_and_gate_ot_hybrid_correct`
- `gmw_real_ideal_view_eq`
- `gmw_ot_hybrid_uc_secure_perfect`

这里的 GMW 证明边界是：

- OT-hybrid world
- 静态半诚实
- 同步轮次
- 完美 UC 安全

实现上，真实协议和模拟器都被写成“按腐化情形产生局部可观察执行分布”的事件驱动生成器。  
特别地，左/右单边 simulator 只依赖：

- 被腐化方输入
- 理想输出
- 自己采样的随机种子

不会读取诚实方输入，也不会重放真实执行 witness。

## 如何构建

在项目根目录执行：

```bash
cd lean-crypto-protocols
lake build
```

如果只想单独检查 GMW：

```bash
lake build LeanCryptoProtocols.GMW.OTHybrid
```

## 当前限制

当前还没有实现：

- 恶意敌手
- 自适应腐化
- 完整 Canetti 异步调度语义
- real-world OT 协议与组合定理
- 真实 PPT / negligible 上的完整计算安全实例证明

这些是后续工作。

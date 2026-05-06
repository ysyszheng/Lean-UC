# lean-crypto-protocols Agent Notes

本文件给后续进入本仓库工作的 coding agent 使用。

目标不是介绍全部数学背景，而是给出：

- 当前项目主线在做什么；
- 哪些模块是主路径；
- 代码/注释/命名规范；
- 近期已经反复澄清过、容易被误改的约束。

## 1. 项目目标

这是一个用 Lean 形式化隐私计算协议与 UC 安全证明的项目。

当前主线不是旧的 “直接返回 view 分布” 风格，而是按 Canetti 2000 Section 2
重建 UC 框架，核心关键词是：

- machine
- protocol
- controller-driven execution
- ideal functionality
- ideal protocol
- UC-emulate / UC-realize

当前安全模型边界：

- `n` 方
- static corruption
- semi-honest
- uniform model
- 同步加密授权通信

## 2. 当前主线模块

优先看这些文件：

- `LeanCryptoProtocols/UC/Machine.lean`
- `LeanCryptoProtocols/UC/Controller.lean`
- `LeanCryptoProtocols/UC/IdealWorld.lean`
- `LeanCryptoProtocols/UC/Security.lean`
- `LeanCryptoProtocols/UC/Indistinguishability.lean`
- `LeanCryptoProtocols/UC/Functionality/OT.lean`
- `LeanCryptoProtocols/Assumptions/DDH.lean`
- `LeanCryptoProtocols/Config.lean`

其它旧模块可能仍在仓库里，但不一定已经迁移到当前主线语义。
如果 README、旧注释、旧证明和当前主线代码不一致，以当前主线代码为准。

## 3. 命名规范

统一遵循：

- 结构、归纳类型、类型别名、模块入口：`CamelCase`
- `def` / `theorem` / helper / 字段 / 局部工具函数：`snake_case`

例子：

- `IdealFunctionality`
- `ExecutionSetup`
- `OTSenderInput`
- `max_controller_steps`
- `ddh_assumption`
- `warn_if_budget_exceeded`

不要把普通 `def` 写成 `camelCase`，除非它本身是构造子或类型名的一部分。

## 4. 注释规范

- 代码注释和模块文档默认使用中文。
- 数学术语、协议名、Lean 标识符可保留英文。
- 不要无意义注释；只写有审计价值、建模价值、或说明设计边界的注释。
- 不要擅自删除用户已经写下的 TODO 标识或 TODO 文本。
  - 如果对应代码整段被删除，可以同步删去失效 TODO。
  - 如果代码还在，保留 TODO 原文。

## 5. Machine / Protocol 约束

这些约束非常重要，容易被误改：

### 5.1 `MachineProgram`

`receive` 只能接收 `Message Payload`，不能看到 `Envelope` 或端口信息。

原因：

- machine 收到消息时只能看到消息内容；
- 路由和端口检查属于 controller 的职责，不属于 machine 本地程序。

### 5.2 `Message` 与 `Envelope`

当前通信对象分两层：

- `Message`：`source` / `label` / `payload`
- `Envelope`：`port` / `message` / `label_matches`

`Envelope` 负责说明消息发往哪个 `CommPort`；
`Message` 负责说明消息内容是什么。

### 5.3 `Protocol`

当前用 `Protocol`，不是旧的 `ProtocolShape`。

`Protocol` 是 protocol-only 的静态结构。
协议内 machine 的静态 `communication_set` 不应直接与 environment 或 adversary 通信；
这类运行时 backdoor 连边由 controller overlay 注入。

### 5.4 `MachineId`

- `MachineId = Nat`
- `env_id = 0`
- `adv_id = 1`

不要回退到前缀式 `List Nat` 身份编码。
caller / subroutine / subsidiary 关系通过 communication set 和 protocol machine 集合推出。

## 6. Controller 约束

`Controller.exec` 是当前 uniform 模型下的执行 ensemble 来源。

注意两点：

### 6.1 安全参数 `n`

在当前主线里，`n` 是安全参数索引，不用于真的限制 machine 只能执行 poly(`n`) 步。

controller 的执行预算使用配置常数：

- `LeanCryptoProtocols.max_controller_steps`

如果预算耗尽，应通过命令行 wrapper 提醒，而不是把 IO 副作用塞进纯定义里。

### 6.2 environment / adversary 初始通信

初始静态配置里，environment 和 adversary 只保留彼此之间的 backdoor 通信端口。

执行初始化后，controller 的 runtime overlay 会动态补上：

- environment 到各 main machine 的输入端口
- adversary 到被腐化 machine 的 backdoor 端口
- 被腐化 machine 到 adversary 的 backdoor 端口

不要把这些运行时端口重新写回 protocol 的静态 `communication_set`。

## 7. Ideal World 约束

### 7.1 `IdealFunctionality`

`IdealFunctionality` 只是一个 functionality machine 加若干用于自动构造 ideal world 的辅助字段。

### 7.2 Dummy party

dummy party 不是手写任意 machine；其职责是机械转发：

- 收到外部输入后，包装后转发给 functionality
- 收到 functionality 输出后，拆包并转发给目标 external identity

不要把 dummy party 写成能看到额外隐私信息的模拟器接口。

### 7.3 `UCRealizesAt`

`UCRealizesAt` realize 的对象是 `IdealFunctionality`。

ideal protocol 由 builder 自动生成：

- `mk_dummy_party`
- `mk_dummy_parties`
- `mk_ideal_protocol`

不要把 `UCRealizesAt` 改回 “realize 某个手工给定的 IdealProtocol”。

## 8. 不可区分与复杂度接口

当前统一使用：

- `PerfectIndist`
- `StatisticalIndist`
- `ComputationalIndist`
- `PPT`
- `Negligible`

数学记号：

- `≡`
- `≈ₛ`
- `≈_c`

当前是 uniform 模型：

- `Ensemble α = ℕ → PMF α`
- `Distinguisher α` 不接收额外 `Aux`

不要把主线重新改回 non-uniform `Aux` 接口，除非用户明确要求。

## 9. OT 模块约束

`LeanCryptoProtocols/UC/Functionality/OT.lean` 当前已经切到 message-driven ideal functionality。

关键点：

- 使用 `sid` 表示 protocol session
- 使用 `ssid` 表示该 session 内的 OT 子会话
- OT functionality 的内部状态按 `(sid, ssid)` 记录 sender/receiver 请求
- 重复请求当前策略是：首个值生效，后续同类请求忽略

如无明确要求，不要改这个异常处理策略。

## 10. DDH 假设模块

`LeanCryptoProtocols/Assumptions/DDH.lean` 用于后续 reduction。

当前接口是抽象的：

- 群生成算法按安全参数 `n` 输出 group description
- DDH 真分布与随机分布都定义为 ensemble
- 假设写成计算不可区分

后续若做 reduction，应优先在这个层面复用：

- `GroupGenerator`
- `PPTGroupGenerator`
- `ddh_real`
- `ddh_random`
- `ddh_assumption`

## 11. 修改代码时的工作方式

- 优先做小而局部的修改。
- 不要顺手大改无关文件。
- 如果用户只要求改几个文件，就只改那几个文件。
- 若发现旧模块和主线框架不兼容，不要静默“全仓重构”；先把当前任务做好。

对 proof / 定义占位：

- 尽量给真实构造，不要新增 `axiom` 占位。
- 如果必须临时占位，要非常明确，并尽快替换。

## 12. 构建建议

修改后优先做局部构建，而不是每次都全量构建：

- `lake build LeanCryptoProtocols.UC.Controller`
- `lake build LeanCryptoProtocols.UC.IdealWorld`
- `lake build LeanCryptoProtocols.UC.Security`
- `lake build LeanCryptoProtocols.UC.Functionality.OT`
- `lake build LeanCryptoProtocols.Assumptions.DDH`

如果任务只涉及单文件，也可以先用：

- `lake env lean <file>`

## 13. 给后续 agent 的默认判断

如果你是后续进入这个仓库的 agent，默认按下面的优先级理解项目：

1. 当前代码中的主线 UC 模块
2. 本文件 `AGENTS.md`
3. `README.md`
4. 旧的协议实例或旧注释

如果发现冲突，优先保持当前主线代码的一致性，并在改动说明里明确写出你依据的是哪一层。

import LeanCryptoProtocols.UC.Machine
import LeanCryptoProtocols.UC.Indistinguishability

/-!
# UC-emulate / ideal protocol / UC-realize

本文件在 `Machine.lean` 的静态语法之上加入：

- environment；
- adversary / simulator；
- executable protocol；
- ideal functionality / dummy party / ideal protocol；
- UC-emulate；
- UC-realize。

这里的框架固定在 Section 2 的简化 setting：

- static corruption；
- semi-honest；
- 同步加密授权通信；
- uniform：不建模 environment 的额外辅助输入，只保留安全参数 `n`。

按 Canetti 第 2.2.2 节的组织：

- ideal functionality 只是一个 machine；
- ideal protocol 是由若干 dummy parties 与 ideal functionality 组成的协议。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- 环境本身也是一个 machine。 -/
structure Environment (Payload : Type u) where
  machine : Machine Payload Bool
  id_matches : machine.id = envId
  -- 约束：环境能和敌手通信
  canCommunicateWithAdversary :
    ∃ m ∈ machine.communicationSet, m.dest = advId

/--
半诚实、静态腐化敌手。

这里不再给敌手开放主动篡改 honest program 的接口；它只携带：

- 一个 adversary machine；
- 初始腐化集合。
-/
structure Adversary (Payload : Type u) where
  machine : Machine Payload PUnit
  corruptionSet : Finset MachineId
  id_matches : machine.id = advId
  -- 约束：adversary 只能给 corruptionSet 中的 machine 以及环境发送/接收 backdoor 消息
  -- m.label = .backdoor 的约束已经隐含在 CommPort 的 WellFormed 里了
  backdoorOnlyToCorrupted :
    (∀ p ∈ machine.communicationSet → (p.dest ∈ corruptionSet ∪ {envId})) ∧
      (∀ m ∈ corruptionSet ∪ {envId}, ∃ p ∈ machine.communicationSet, p.dest = m)

/-- simulator 在 Section 2 的理想世界中扮演 adversary 的角色。 -/
abbrev Simulator (Payload : Type u) := Adversary Payload

/-- 可执行协议：协议 + 敌手 + 环境。 -/
structure ExecutableProtocol (Payload : Type u)
    extends ProtocolShape Payload where
  adversary : Adversary Payload
  environment : Environment Payload
  exec :
    ℕ →
    PMF Bool -- TODO: 放到controller里面
  -- 约束：环境除了和敌手通信之外，只能和协议中的 main machine 发送input。
  env_communication_constraints :
    ∀ m ∈ env.machine.communicationSet,
      m.dest ≠ advId →
        (toProtocolShape.IsMainMachine m.dest ∧ m.label = .input)
  -- 约束：敌手的 corruptionSet 必须是协议中 machine identity 的子集。
  adversary_corruption_constraints :
    adversary.corruptionSet ⊆ toProtocolShape.machineIds.toFinset
  -- 约束：敌手的 corruptionSet 中的 machine 能和敌手通信。
  communication_with_adversary :
    ∀ m ∈ toProtocolShape.machines, m.id ∈ adversary.corruptionSet →
      ∃ p ∈ m.communicationSet, p.dest = advId

/-- `exec_{π,A,E}` 诱导出的输出 ensemble。 -/
def ExecEnsemble {Payload : Type u}
    (π : ExecutableProtocol Payload)
    (A : Adversary Payload)
    (E : Environment Payload) : Ensemble Bool :=
  fun n => π.exec A E n

/-- 真实协议与理想协议在固定 `A,S,E,n` 下的执行差。 -/
noncomputable def ExecDiff {Payload : Type u}
    (π φ : ExecutableProtocol Payload)
    (A : Adversary Payload)
    (S : Simulator Payload)
    (E : Environment Payload)
    (n : ℕ) : ℝ :=
  |probTrue (π.exec A E n) - probTrue (φ.exec S E n)|

/--
理想功能对象。

按 Canetti 原文，ideal functionality 本身只是一个 machine。
-/
structure IdealFunctionality (Payload : Type u) where
  dummyPartyCount : ℕ
  machine : Machine Payload PUnit
  functionalityId : MachineId
  id_matches : machine.2.id = functionalityId

-- TODO：从IdealFunctionality make ideal protocol，构造dummyPartyCount个dummy parties，program就是转发消息（给环境可以吗）

/--
dummy party。

这一层显式记录 dummy party 的 identity、其对应的 ideal functionality identity，
以及它应满足的最小语义约束：

- 收到输入后转发给功能机；
- 收到功能机的输出后转发给目标 identity；
- 忽略 backdoor 信息。
-/
structure DummyParty (Payload : Type u) where
  machine : Machine Payload PUnit
  partyId : MachineId
  id_matches : machine.id = partyId
  -- 约束：dummy party 只不能和敌手直接通信。还有一些涉及协议的约束放在idealProtocol中。
  noBackdoor :
    ∀ m ∈ machine.communicationSet, m.label = .backdoor → False

/-- 将 dummy party 打包成异质 machine。 -/
def DummyParty.toAnyMachine {Payload : Type u} (d : DummyParty Payload) : AnyMachine Payload :=
  ⟨PUnit, d.machine⟩

/--
ideal protocol。

按 Canetti 原文，它由：

- 若干 dummy parties；
- 一个 ideal functionality machine；

共同组成。其 main machines 是 dummy parties，而功能机本身是 internal machine。
-/
structure IdealProtocol (Payload : Type u)
    extends ExecutableProtocol Payload where
  functionality : IdealFunctionality Payload
  dummyParties : List (DummyParty Payload)
  parties_count :
    dummyParties.length = functionality.dummyPartyCount
  machines_eq :
    toExecutableProtocol.toProtocolShape.machines =
      dummyParties.map DummyParty.toAnyMachine ++ [functionality.machine]
  -- DummyParty 的通信约束：input 消息只能向功能机发送，dummy party 之间不能直接通信。
  dummy_communication_constraints :
    ∀ d ∈ dummyParties, ∀ p ∈ d.machine.communicationSet,
      (p.dest ∉ (dummyParties.map DummyParty.partyId).toFinset) ∧
      (p.label = PortLabel.input ↔ p.dest = functionality.functionalityId)
  -- ideal functionality 的通信约束：功能机只能给 dummy party 发送 subroutineOutput 消息，或者给敌手发送 backdoor 消息。
  functionality_communication_constraints :
    ∀ p ∈ functionality.machine.communicationSet,
      (p.dest ∈ (dummyParties.map DummyParty.partyId).toFinset ∧ p.label = PortLabel.subroutineOutput) ∨
      (p.dest = advId ∧ p.label = PortLabel.backdoor)
  dummy_are_main :
    ∀ d ∈ dummyParties,
      toExecutableProtocol.toProtocolShape.IsMainMachine d.partyId
  functionality_is_internal :
    toExecutableProtocol.toProtocolShape.IsInternalMachine functionality.functionalityId

/-- ideal protocol 中 dummy party identities 的集合。 -/
def IdealProtocol.dummyPartyIds {Payload : Type u}
    (Φ : IdealProtocol Payload) : Finset MachineId :=
  (Φ.dummyParties.map DummyParty.partyId).toFinset

/--
UC-emulate：对任意 adversary，都存在 simulator，使得对任意 environment，
真实协议与目标协议的环境输出满足 restricted-model 的不可区分要求。

这里只有计算层要求 `PPT`。
-/
def UCEmulatesAt {Payload : Type u}
    (level : SecurityLevel)
    (π φ : ExecutableProtocol Payload) : Prop :=
  match level with
  | .perfect =>
      ∀ A : Adversary Payload, ∃ S : Simulator Payload,
        ∀ E : Environment Payload, ∀ n,
          π.exec A E n = φ.exec S E n
  | .statistical =>
      ∀ A : Adversary Payload, ∃ S : Simulator Payload,
        ∀ E : Environment Payload,
          ∃ negl, Negligible negl ∧ ∀ n, ExecDiff π φ A S E n ≤ negl n
  | .computational =>
      ∀ A : Adversary Payload, PPT A →
        ∃ S : Simulator Payload, PPT S ∧
          ∀ E : Environment Payload, PPT E →
            ∃ negl, Negligible negl ∧ ∀ n, ExecDiff π φ A S E n ≤ negl n

/-- 常用简写。 -/
def UCEmulatesPerfect {Payload : Type u}
    (π φ : ExecutableProtocol Payload) : Prop :=
  UCEmulatesAt .perfect π φ

def UCEmulatesStatistical {Payload : Type u}
    (π φ : ExecutableProtocol Payload) : Prop :=
  UCEmulatesAt .statistical π φ

def UCEmulatesComputational {Payload : Type u}
    (π φ : ExecutableProtocol Payload) : Prop :=
  UCEmulatesAt .computational π φ

/--
UC-realize：协议 `π` UC-emulate 一个理想协议 `Φ`。
-- TODO：换成从IdealFunctionality make ideal protocol
-/
def UCRealizesAt {Payload : Type u}
    (level : SecurityLevel)
    (π : ExecutableProtocol Payload)
    (Φ : IdealProtocol Payload) : Prop :=
  UCEmulatesAt level π Φ.toExecutableProtocol

/-- 常用简写。 -/
def UCRealizesPerfect {Payload : Type u}
    (π : ExecutableProtocol Payload)
    (Φ : IdealProtocol Payload) : Prop :=
  UCRealizesAt .perfect π Φ

def UCRealizesStatistical {Payload : Type u}
    (π : ExecutableProtocol Payload)
    (Φ : IdealProtocol Payload) : Prop :=
  UCRealizesAt .statistical π Φ

def UCRealizesComputational {Payload : Type u}
    (π : ExecutableProtocol Payload)
    (Φ : IdealProtocol Payload) : Prop :=
  UCRealizesAt .computational π Φ

end LeanCryptoProtocols.UC

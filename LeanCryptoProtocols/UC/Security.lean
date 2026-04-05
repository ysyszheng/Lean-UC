import LeanCryptoProtocols.UC.Machine
import LeanCryptoProtocols.UC.Indistinguishability

/-!
# UC-emulate / ideal protocol / UC-realize

本文件在 `Machine.lean` 的静态语法之上加入：

- environment；
- adversary / simulator；
- executable protocol；
- ideal functionality / ideal protocol；
- UC-emulate；
- UC-realize。

这里的框架固定在 Section 2 的简化 setting：

- static corruption；
- semi-honest；
- 同步加密授权通信。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- 环境本身也是一个 machine。 -/
structure Environment (Payload : Type u) (Aux : Type u) where
  machine : Machine Payload Bool

/--
半诚实、静态腐化敌手。

这里不再给敌手开放主动篡改 honest program 的接口；它只携带：

- 一个 adversary machine；
- 初始腐化集合。
-/
structure Adversary (Payload : Type u) where
  machine : Machine Payload PUnit
  corruptionSet : Finset MachineId

/-- simulator 在 Section 2 的理想世界中扮演 adversary 的角色。 -/
abbrev Simulator (Payload : Type u) :=
  Adversary Payload

/-- 可执行协议：静态结构 + 环境输出分布。 -/
structure ExecutableProtocol (Payload : Type u) (Aux : Type u)
    extends ProtocolShape Payload where
  exec :
    Adversary Payload →
    Environment Payload Aux →
    Aux →
    ℕ →
    PMF Bool

/-- `exec_{π,A,E}` 诱导出的输出 ensemble。 -/
def ExecEnsemble {Payload : Type u} {Aux : Type u}
    (π : ExecutableProtocol Payload Aux)
    (A : Adversary Payload)
    (E : Environment Payload Aux) : Ensemble Aux Bool :=
  fun z n => π.exec A E z n

/--
理想功能对象。

`mkIdealProtocol S` 返回把 simulator `S` 接到理想世界后形成的 ideal protocol。
-/
structure IdealFunctionality (Payload : Type u) (Aux : Type u) where
  functionality : AnyMachine Payload
  functionalityId : MachineId
  dummyPartyIds : Finset MachineId
  mkIdealProtocol : Simulator Payload → ExecutableProtocol Payload Aux
  functionality_id_matches : functionality.2.id = functionalityId

/-- 从理想功能和 simulator 构造 ideal protocol。 -/
def IdealProtocol {Payload : Type u} {Aux : Type u}
    (F : IdealFunctionality Payload Aux)
    (S : Simulator Payload) : ExecutableProtocol Payload Aux :=
  F.mkIdealProtocol S

/--
UC-emulate：对任意 adversary，都存在 simulator，使得对任意 environment，
真实协议与目标协议的环境输出不可区分。

在三层语义上，这里分别对应：
TODO: 这里有错，完美和统计层不需要PPT
- 完美层：`ExecEnsemble π A E ≡ ExecEnsemble φ S E`
- 统计层：`ExecEnsemble π A E ≈ₛ ExecEnsemble φ S E`
- 计算层：`ExecEnsemble π A E ≈_c ExecEnsemble φ S E`
-/
def UCEmulatesAt {Payload : Type u} {Aux : Type u}
    (level : SecurityLevel)
    (π φ : ExecutableProtocol Payload Aux) : Prop :=
  ∀ A, PPT A → ∃ S : Simulator Payload, PPT S ∧
    ∀ E, PPT E →
      Indistinguishable level
        (ExecEnsemble π A E)
        (ExecEnsemble φ S E)

/-- 完美层的常用简写。 -/
def UCEmulatesPerfect {Payload : Type u} {Aux : Type u}
    (π φ : ExecutableProtocol Payload Aux) : Prop :=
  UCEmulatesAt .perfect π φ

/--
UC-realize：协议 `π` UC-emulate 由理想功能 `F` 诱导出的 ideal protocol。

完美、统计、计算三层分别记为 `≡`、`≈ₛ`、`≈_c`。
-/
def UCRealizesAt {Payload : Type u} {Aux : Type u}
    (level : SecurityLevel)
    (π : ExecutableProtocol Payload Aux)
    (F : IdealFunctionality Payload Aux) : Prop :=
  ∀ A, PPT A → ∃ S : Simulator Payload, PPT S ∧
    ∀ E, PPT E →
      Indistinguishable level
        (ExecEnsemble π A E)
        (ExecEnsemble (IdealProtocol F S) S E)

/-- 完美 UC realize 的常用简写。 -/
def UCRealizesPerfect {Payload : Type u} {Aux : Type u}
    (π : ExecutableProtocol Payload Aux)
    (F : IdealFunctionality Payload Aux) : Prop :=
  UCRealizesAt .perfect π F

end LeanCryptoProtocols.UC

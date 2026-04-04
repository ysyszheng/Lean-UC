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
- authenticated communication。
-/

universe u v

namespace LeanCryptoProtocols.UC

/-- 环境本身也是一个 machine。 -/
structure Environment (Label : Type u) (Payload : Type v) (Aux : Type u) where
  machine : Machine Label Payload Bool

/--
半诚实、静态腐化敌手。

这里不再给敌手开放主动篡改 honest program 的接口；它只携带：

- 一个 adversary machine；
- 初始腐化集合。
-/
structure Adversary (Label : Type u) (Payload : Type v) where
  machine : Machine Label Payload PUnit
  corruptionSet : Finset MachineId

/-- simulator 在 Section 2 的理想世界中扮演 adversary 的角色。 -/
abbrev Simulator (Label : Type u) (Payload : Type v) :=
  Adversary Label Payload

/-- 可执行协议：静态结构 + 环境输出分布。 -/
structure ExecutableProtocol (Label : Type u) (Payload : Type v) (Aux : Type u)
    extends ProtocolShape Label Payload where
  exec :
    Adversary Label Payload →
    Environment Label Payload Aux →
    Aux →
    ℕ →
    PMF Bool

/-- `exec_{π,A,E}` 诱导出的输出 ensemble。 -/
def ExecEnsemble {Label : Type u} {Payload : Type v} {Aux : Type u}
    (π : ExecutableProtocol Label Payload Aux)
    (A : Adversary Label Payload)
    (E : Environment Label Payload Aux) : Ensemble Aux :=
  fun z n => π.exec A E z n

/--
理想功能对象。

`mkIdealProtocol S` 返回把 simulator `S` 接到理想世界后形成的 ideal protocol。
-/
structure IdealFunctionality (Label : Type u) (Payload : Type v) (Aux : Type u) where
  functionality : AnyMachine Label Payload
  functionalityId : MachineId
  dummyPartyIds : Finset MachineId
  mkIdealProtocol : Simulator Label Payload → ExecutableProtocol Label Payload Aux
  functionality_id_matches : functionality.2.id = functionalityId

/-- 从理想功能和 simulator 构造 ideal protocol。 -/
def IdealProtocol {Label : Type u} {Payload : Type v} {Aux : Type u}
    (F : IdealFunctionality Label Payload Aux)
    (S : Simulator Label Payload) : ExecutableProtocol Label Payload Aux :=
  F.mkIdealProtocol S

/--
UC-emulate：对任意 adversary，都存在 simulator，使得对任意 environment，
真实协议与目标协议的环境输出不可区分。
-/
def UCEmulatesAt {Label : Type u} {Payload : Type v} {Aux : Type u}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTAdv : Adversary Label Payload → Prop)
    (PPTEnv : Environment Label Payload Aux → Prop)
    (π φ : ExecutableProtocol Label Payload Aux) : Prop :=
  ∀ A, PPTAdv A → ∃ S : Simulator Label Payload, PPTAdv S ∧
    ∀ E, PPTEnv E →
      Indistinguishable level ε
        (ExecEnsemble π A E)
        (ExecEnsemble φ S E)

/-- 完美层的常用简写。 -/
def UCEmulatesPerfect {Label : Type u} {Payload : Type v} {Aux : Type u}
    (π φ : ExecutableProtocol Label Payload Aux) : Prop :=
  UCEmulatesAt .perfect zeroError (fun _ => True) (fun _ => True) π φ

/--
UC-realize：协议 `π` UC-emulate 由理想功能 `F` 诱导出的 ideal protocol。
-/
def UCRealizesAt {Label : Type u} {Payload : Type v} {Aux : Type u}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTAdv : Adversary Label Payload → Prop)
    (PPTEnv : Environment Label Payload Aux → Prop)
    (π : ExecutableProtocol Label Payload Aux)
    (F : IdealFunctionality Label Payload Aux) : Prop :=
  ∀ A, PPTAdv A → ∃ S : Simulator Label Payload, PPTAdv S ∧
    ∀ E, PPTEnv E →
      Indistinguishable level ε
        (ExecEnsemble π A E)
        (ExecEnsemble (IdealProtocol F S) S E)

/-- 完美 UC realize 的常用简写。 -/
def UCRealizesPerfect {Label : Type u} {Payload : Type v} {Aux : Type u}
    (π : ExecutableProtocol Label Payload Aux)
    (F : IdealFunctionality Label Payload Aux) : Prop :=
  UCRealizesAt .perfect zeroError (fun _ => True) (fun _ => True) π F

end LeanCryptoProtocols.UC

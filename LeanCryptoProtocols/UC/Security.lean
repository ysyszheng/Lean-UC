import LeanCryptoProtocols.UC.Controller

/-!
# UC-emulate / ideal functionality / UC-realize

本文件建立在 `Machine.lean` 与 `Controller.lean` 之上，给出：

TODO: 拆分成两个文件，分别处理理想功能和UC-emulate/realize

- 理想功能；
- dummy party；
- 从理想功能自动生成 ideal protocol 的构造接口；
- UC-emulate；
- UC-realize。

这里固定采用 uniform 的 restricted model：不显式建模额外辅助输入，只保留安全参数 `n`。
-/

universe u

namespace LeanCryptoProtocols.UC

/--
理想功能对象。

按 Canetti 原文，理想功能本身只是一个 machine；但为了能自动构造 dummy parties，
这里额外记录：

- 参与方 identities；
- 每个参与方对应的 external identities；
- 如何把环境输入包装成送给功能机的 payload；
- 如何把功能机返回的 payload 解析成目标 identity 与外发 payload。
-/
structure IdealFunctionality (Payload : Type u) where
  party_ids : List MachineId
  functionality_id : MachineId
  machine : Machine Payload Unit
  id_matches : machine.id = functionality_id
  party_ids_nodup : party_ids.Nodup
  parties_separated : env_id ∉ party_ids ∧ adv_id ∉ party_ids
  functionality_separated : functionality_id ≠ env_id ∧ functionality_id ≠ adv_id
  functionality_not_party : functionality_id ∉ party_ids
  party_external_ids : MachineId → Finset MachineId
  external_ids_nonempty :
    ∀ pid ∈ party_ids, (party_external_ids pid).Nonempty
  external_ids_outside_parties :
    ∀ pid ∈ party_ids, ∀ ext ∈ party_external_ids pid, ext ∉ party_ids
  external_ids_separated :
    ∀ pid ∈ party_ids, ∀ ext ∈ party_external_ids pid,
      ext ≠ functionality_id ∧ ext ≠ env_id ∧ ext ≠ adv_id
  wrap_input : Option MachineId → Payload → Payload
  unwrap_output : Payload → Option (MachineId × Payload)
  functionality_ports_to_parties :
    ∀ pid ∈ party_ids,
      ∃ p ∈ machine.communication_set, p.dest = pid ∧ p.label = .subroutineOutput
  functionality_comm_constraints :
    ∀ p ∈ machine.communication_set,
      p.dest ∈ party_ids.toFinset ∧ p.label = .subroutineOutput
  -- TODO: functionality还可以和敌手通信。这个是在构造ExecutionSetup时通过给敌手的corruptionSet加入functionality的ID，后续调用runtime_communication_set动态实现吗

/--
dummy party。

这是 `mk_dummy_party` 的审计输出对象，而不是协议设计者需要手写的主入口。
-/
structure DummyParty (Payload : Type u) where
  party_id : MachineId
  functionality_id : MachineId
  external_ids : Finset MachineId
  machine : Machine Payload Unit
  id_matches : machine.id = party_id
  no_backdoor :
    ∀ p ∈ machine.communication_set, p.label = .backdoor → False
  input_port_present :
    ∃ p ∈ machine.communication_set, p.dest = functionality_id ∧ p.label = .input
  external_ports_complete :
    ∀ ext ∈ external_ids,
      ∃ p ∈ machine.communication_set, p.dest = ext ∧ p.label = .subroutineOutput
  communication_constraints :
    ∀ p ∈ machine.communication_set,
      (p.dest = functionality_id ∧ p.label = .input) ∨
        (p.dest ∈ external_ids ∧ p.label = .subroutineOutput)

/-- 把 dummy party 打包成异质 machine。 -/
def DummyParty.to_any_machine {Payload : Type u} (d : DummyParty Payload) : AnyMachine Payload :=
  ⟨Unit, d.machine⟩

/-- 从理想功能自动生成一个 dummy party。 -/
-- TODO: 这个和下面的总共3个axiom有什么用？没有定义如何构造的过程，也没有指明DummyParty的 machine的program只是做转发的功能
axiom mk_dummy_party {Payload : Type u}
    (f : IdealFunctionality Payload) (party_id : MachineId)
    (h_party : party_id ∈ f.party_ids) : DummyParty Payload

/--
ideal protocol。

它由若干 dummy parties 与一个理想功能机组成；这里显式暴露这三部分，
便于后续审计。
-/
structure IdealProtocol (Payload : Type u) where
  protocol : Protocol Payload
  functionality : IdealFunctionality Payload
  dummy_parties : List (DummyParty Payload)
  machines_eq :
    protocol.machines =
      dummy_parties.map DummyParty.to_any_machine ++ [⟨Unit, functionality.machine⟩]

/-- 从理想功能的参与方列表自动生成所有 dummy parties。 -/
axiom mk_dummy_parties {Payload : Type u}
    (f : IdealFunctionality Payload) : List (DummyParty Payload)

/--
从理想功能自动生成 ideal protocol。

这里把 proof-heavy 的 protocol-shape 组装集中放在一个构造器里，供 `UCRealizesAt`
复用。
-/
axiom mk_ideal_protocol {Payload : Type u} :
  IdealFunctionality Payload → IdealProtocol Payload

/-- 真实世界与理想世界在固定 `A,S,E,n` 下的执行差。 -/
noncomputable def exec_diff {Payload : Type u}
    {π φ : Protocol Payload}
    {A : Adversary Payload}
    {S : Simulator Payload}
    {E : Environment Payload}
    (real_setup : ExecutionSetup π A E)
    (ideal_setup : ExecutionSetup φ S E)
    (n : ℕ) : ℝ :=
  |probTrue (Controller.exec real_setup n) - probTrue (Controller.exec ideal_setup n)|

/--
UC-emulate：对任意 adversary，都存在 simulator，使得对任意 environment，
真实协议与目标协议的环境输出满足 restricted-model 的不可区分要求。

这里把依赖 `protocol + adversary + environment` 的合法性检查显式编码进
`ExecutionSetup` 参数。
-/
def UCEmulatesAt {Payload : Type u}
    (level : SecurityLevel)
    (π φ : Protocol Payload) : Prop :=
  match level with
  | .perfect =>
      ∀ A : Adversary Payload, ∃ S : Simulator Payload,
        ∀ E : Environment Payload,
          ∀ real_setup : ExecutionSetup π A E, -- TODO: 这里为什么要 forall？ExecutionSetup π A E应该是根据π A E自动得出的。forall是为了保证进入后面分析的π A E都满足ExecutionSetup的约束（否则ExecutionSetup无法构造出来）吗？
            ∀ ideal_setup : ExecutionSetup φ S E,
              ∀ n, Controller.exec real_setup n = Controller.exec ideal_setup n
  | .statistical =>
      ∀ A : Adversary Payload, ∃ S : Simulator Payload,
        ∀ E : Environment Payload,
          ∀ real_setup : ExecutionSetup π A E,
            ∀ ideal_setup : ExecutionSetup φ S E,
              ∃ negl, Negligible negl ∧
                ∀ n, exec_diff real_setup ideal_setup n ≤ negl n
  | .computational =>
      ∀ A : Adversary Payload, PPT A →
        ∃ S : Simulator Payload, PPT S ∧
          ∀ E : Environment Payload, PPT E →
            ∀ real_setup : ExecutionSetup π A E,
              ∀ ideal_setup : ExecutionSetup φ S E,
                ∃ negl, Negligible negl ∧
                  ∀ n, exec_diff real_setup ideal_setup n ≤ negl n

/-- 常用简写。 -/
def UCEmulatesPerfect {Payload : Type u}
    (π φ : Protocol Payload) : Prop :=
  UCEmulatesAt .perfect π φ

def UCEmulatesStatistical {Payload : Type u}
    (π φ : Protocol Payload) : Prop :=
  UCEmulatesAt .statistical π φ

def UCEmulatesComputational {Payload : Type u}
    (π φ : Protocol Payload) : Prop :=
  UCEmulatesAt .computational π φ

/--
UC-realize：协议 `π` UC-emulate 从 `F` 自动构造出的 ideal protocol。
-/
def UCRealizesAt {Payload : Type u}
    (level : SecurityLevel)
    (π : Protocol Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCEmulatesAt level π (mk_ideal_protocol f).protocol

/-- 常用简写。 -/
def UCRealizesPerfect {Payload : Type u}
    (π : Protocol Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .perfect π f

def UCRealizesStatistical {Payload : Type u}
    (π : Protocol Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .statistical π f

def UCRealizesComputational {Payload : Type u}
    (π : Protocol Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .computational π f

end LeanCryptoProtocols.UC

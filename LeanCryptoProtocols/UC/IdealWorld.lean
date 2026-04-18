import LeanCryptoProtocols.UC.Controller

/-!
# 理想功能 / dummy party / ideal protocol

本文件建立在 `Machine.lean` 与 `Controller.lean` 之上，给出：

- 理想功能；
- dummy party；
- 从理想功能自动生成 ideal protocol 的构造接口。

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

end LeanCryptoProtocols.UC

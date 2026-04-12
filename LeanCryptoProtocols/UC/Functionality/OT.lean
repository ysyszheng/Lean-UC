import LeanCryptoProtocols.UC.Security

/-!
# 两方 1-out-of-2 OT 理想功能

本文件按新的 message-driven / controller-driven 接口，给出两方 bit OT 的理想功能。

这里：

- `F_OT` 只保留值语义；
- `IdealOT` 返回一个 `IdealFunctionality`；
- 具体的 ideal protocol 由 `mk_ideal_protocol` 自动从 `IdealOT` 生成。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- OT 发送方输入的两个 bit。 -/
structure OTSenderInput where
  m0 : Bool
  m1 : Bool
  deriving Repr, DecidableEq

/-- OT 接收方输入的选择位。 -/
abbrev OTReceiverInput : Type := Bool

/-- OT 接收方输出。 -/
abbrev OTOutput : Type := Bool

/-- 单次 OT 的值语义。 -/
def F_OT (sender : OTSenderInput) (choice : OTReceiverInput) : OTOutput :=
  cond choice sender.m1 sender.m0

/-- OT 的业务消息体。 -/
inductive OTBody where
  | sender_req (call_id : Nat) (sender : OTSenderInput)
  | receiver_req (call_id : Nat) (choice : OTReceiverInput)
  | receiver_resp (call_id : Nat) (out : OTOutput)
  deriving Repr, DecidableEq

/--
OT 理想世界里统一使用的 payload。

- `plain`：环境与 dummy party 之间的原始业务消息；
- `to_functionality`：dummy party 转发给功能机的消息，额外带上原始调用者 identity；
- `from_functionality`：功能机返回给 dummy party 的消息，额外带上目标 identity。
-/
inductive OTPayload where
  | plain (body : OTBody)
  | to_functionality (caller_source : Option MachineId) (body : OTBody)
  | from_functionality (destination : MachineId) (body : OTBody)
  deriving Repr, DecidableEq

/-- OT 两方与功能机、external identities 的统一命名。 -/
structure OTIds where
  sender_id : MachineId
  receiver_id : MachineId
  functionality_id : MachineId
  sender_external_id : MachineId
  receiver_external_id : MachineId
  sender_ne_receiver : sender_id ≠ receiver_id
  sender_ne_functionality : sender_id ≠ functionality_id
  receiver_ne_functionality : receiver_id ≠ functionality_id
  sender_id_separated : sender_id ≠ env_id ∧ sender_id ≠ adv_id
  receiver_id_separated : receiver_id ≠ env_id ∧ receiver_id ≠ adv_id
  functionality_separated : functionality_id ≠ env_id ∧ functionality_id ≠ adv_id
  sender_external_separated :
    sender_external_id ≠ sender_id ∧
      sender_external_id ≠ receiver_id ∧
      sender_external_id ≠ functionality_id ∧
      sender_external_id ≠ env_id ∧
      sender_external_id ≠ adv_id
  receiver_external_separated :
    receiver_external_id ≠ sender_id ∧
      receiver_external_id ≠ receiver_id ∧
      receiver_external_id ≠ functionality_id ∧
      receiver_external_id ≠ env_id ∧
      receiver_external_id ≠ adv_id

/-- OT 理想功能发往 sender dummy 的端口。 -/
def sender_port (ids : OTIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.sender_id
    (by simpa [Ne, eq_comm] using ids.sender_ne_functionality.symm)
    ids.functionality_separated.2
    ids.sender_id_separated.2

/-- OT 理想功能发往 receiver dummy 的端口。 -/
def receiver_port (ids : OTIds) : CommPort :=
  mk_subroutine_output_port
    ids.functionality_id
    ids.receiver_id
    (by simpa [Ne, eq_comm] using ids.receiver_ne_functionality.symm)
    ids.functionality_separated.2
    ids.receiver_id_separated.2

/--
OT 的理想功能机与其通信包装由 `IdealOT` 统一给出。

这里先固定 OT 的业务消息体、payload 包装类型和参与方/功能机的 identities；
具体的 ideal functionality 机器封装在 `IdealOT` 这个构造器里。
-- TODO: 这个IdealOT有什么用？它不涉及OT的语义？dummy party id是不是要作为参数传入？
-/
axiom IdealOT : OTIds → IdealFunctionality OTPayload

@[simp] theorem F_OT_false (sender : OTSenderInput) :
    F_OT sender false = sender.m0 := by
  rfl

@[simp] theorem F_OT_true (sender : OTSenderInput) :
    F_OT sender true = sender.m1 := by
  rfl

/-- OT 的值语义正确性。 -/
theorem F_OT_correct (sender : OTSenderInput) (choice : Bool) :
    F_OT sender choice = cond choice sender.m1 sender.m0 := by
  rfl

end LeanCryptoProtocols.UC.Functionality

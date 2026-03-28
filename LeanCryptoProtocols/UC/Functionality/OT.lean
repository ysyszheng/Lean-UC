import LeanCryptoProtocols.UC.Core

/-!
# 1-out-of-2 OT 理想功能接口

本文件给出 GMW 在 `F_OT`-hybrid 世界中调用的 bit OT 理想功能。

与此前只定义值函数不同，这里额外显式给出：

- OT 调用输入；
- OT 理想功能返回值；
- 发送方 / 接收方在单次 OT 调用中可见的局部记录；
- OT 作为理想功能时，对不同腐化情形裁剪后的 simulator 可见接口。
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

/-- 单次 OT 调用的完整输入。 -/
structure OTInput where
  sender : OTSenderInput
  choice : OTReceiverInput
  deriving Repr, DecidableEq

/-- 单次 OT 理想功能的值语义。 -/
def F_OT (sender : OTSenderInput) (choice : OTReceiverInput) : OTOutput :=
  cond choice sender.m1 sender.m0

/-- 将 OT 打包成一个理想功能对象。 -/
def IdealOT : IdealFunctionality OTInput OTOutput where
  eval := fun input => F_OT input.sender input.choice
  interface :=
    { CorruptedInput := fun
        | .none => PUnit
        | .left => OTSenderInput
        | .right => OTReceiverInput
        | .both => OTInput
      CorruptedOutput := fun
        | .none => PUnit
        | .left => PUnit
        | .right => OTOutput
        | .both => OTOutput
      Leakage := fun _ => PUnit
      corruptInput := fun
        | .none, _ => PUnit.unit
        | .left, input => input.sender
        | .right, input => input.choice
        | .both, input => input
      corruptOutput := fun
        | .none, _ => PUnit.unit
        | .left, _ => PUnit.unit
        | .right, out => out
        | .both, out => out
      leakage := fun _ _ _ => PUnit.unit }

/-- sender 在单次 OT 调用中可见的信息。 -/
structure OTSenderView where
  callId : Nat
  input : OTSenderInput
  deriving Repr, DecidableEq

/-- receiver 在单次 OT 调用中可见的信息。 -/
structure OTReceiverView where
  callId : Nat
  choice : OTReceiverInput
  output : OTOutput
  deriving Repr, DecidableEq

/-- OT 在协议 trace 中出现的局部事件。 -/
inductive OTLocalEvent where
  | senderCall : OTSenderView → OTLocalEvent
  | receiverCall : OTReceiverView → OTLocalEvent
  deriving Repr, DecidableEq

/-- sender 侧的 OT 局部记录。 -/
def senderView (callId : Nat) (sender : OTSenderInput) : OTSenderView :=
  ⟨callId, sender⟩

/-- receiver 侧的 OT 局部记录。 -/
def receiverView (callId : Nat) (choice : OTReceiverInput) (out : OTOutput) : OTReceiverView :=
  ⟨callId, choice, out⟩

@[simp] theorem F_OT_false (sender : OTSenderInput) :
    F_OT sender false = sender.m0 := by
  rfl

@[simp] theorem F_OT_true (sender : OTSenderInput) :
    F_OT sender true = sender.m1 := by
  rfl

/-- OT 的正确性。 -/
theorem F_OT_correct (sender : OTSenderInput) (choice : Bool) :
    F_OT sender choice = cond choice sender.m1 sender.m0 := by
  rfl

end LeanCryptoProtocols.UC.Functionality

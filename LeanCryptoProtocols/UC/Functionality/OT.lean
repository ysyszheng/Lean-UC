import LeanCryptoProtocols.UC.Core

/-!
# 理想 OT 功能

当前文件给出 GMW 在 `F_OT`-hybrid 世界中所需的最小 OT 理想功能。
第一版只覆盖单次 1-out-of-2 bit OT。
-/

namespace LeanCryptoProtocols.UC.Functionality

/-- OT 发送方输入的两个 bit。 -/
structure OTSenderInput where
  m0 : Bool
  m1 : Bool
  deriving Repr, DecidableEq

/-- OT 接收方的选择位。 -/
abbrev OTReceiverInput : Type := Bool

/-- OT 接收方输出的 bit。 -/
abbrev OTOutput : Type := Bool

/-- 单次 bit OT 的理想功能。 -/
def F_OT (sender : OTSenderInput) (choice : OTReceiverInput) : OTOutput :=
  cond choice sender.m1 sender.m0

@[simp] theorem F_OT_false (sender : OTSenderInput) :
    F_OT sender false = sender.m0 := by
  rfl

@[simp] theorem F_OT_true (sender : OTSenderInput) :
    F_OT sender true = sender.m1 := by
  rfl

/-- OT 的正确性：接收方得到与选择位一致的消息。 -/
theorem F_OT_correct (sender : OTSenderInput) (choice : Bool) :
    F_OT sender choice = cond choice sender.m1 sender.m0 := by
  rfl

end LeanCryptoProtocols.UC.Functionality

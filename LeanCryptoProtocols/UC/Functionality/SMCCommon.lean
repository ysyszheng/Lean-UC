import LeanCryptoProtocols.UC.IdealWorld

/-!
# SMC EasyUC case study 的共享消息类型

本文件集中放置 EasyUC 的 secure message communication case study
需要共用的：

- SMC 会话标识；
- 网络消息；
- `Forw` / `KE` / `SMC` 的业务消息；
- 统一使用的业务 payload 类型。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- SMC protocol session identifier。 -/
abbrev Sid : Type := Nat

/-- case study 里用到的抽象群元素消息。 -/
structure GroupElement where
  value : Nat
  deriving Repr, DecidableEq

/-- case study 里用到的抽象共享密钥。 -/
structure SharedKey where
  value : Nat
  deriving Repr, DecidableEq

/-- case study 里用到的抽象明文。 -/
structure Plaintext where
  value : Bool
  deriving Repr, DecidableEq

/-- case study 里用到的抽象密文。 -/
structure Ciphertext where
  value : Bool
  deriving Repr, DecidableEq

/-- 当前 case study 中用于占位的默认群元素。 -/
def default_group_element : GroupElement := ⟨0⟩

/-- 当前 case study 中用于占位的默认共享密钥。 -/
def default_shared_key : SharedKey := ⟨0⟩

/-- 用共享密钥导出的单 bit pad。 -/
def key_bit (k : SharedKey) : Bool :=
  k.value % 2 = 1

/-- 用于 toy model 的抽象共享密钥派生接口。 -/
def derive_shared_key (g₁ g₂ : GroupElement) : SharedKey :=
  ⟨g₁.value + g₂.value + 1⟩

/-- 当前 case study 中统一使用的抽象加密。 -/
def enc (k : SharedKey) (m : Plaintext) : Ciphertext :=
  ⟨decide (m.value ≠ key_bit k)⟩

/-- 当前 case study 中统一使用的抽象解密。 -/
def dec (k : SharedKey) (c : Ciphertext) : Plaintext :=
  ⟨decide (c.value ≠ key_bit k)⟩

/-- 当前 toy encryption 接口满足 `dec (enc k m) = m`。 -/
theorem dec_enc (k : SharedKey) (m : Plaintext) : dec k (enc k m) = m := by
  cases k with
  | mk kv =>
      cases m with
      | mk mv =>
          change
            Plaintext.mk (decide (decide (mv ≠ key_bit ⟨kv⟩) ≠ key_bit ⟨kv⟩)) =
              Plaintext.mk mv
          cases hkey : key_bit ⟨kv⟩ <;> cases mv <;> rfl

/-- 通过 `Forw` 转发的网络级消息。 -/
inductive NetworkBody where
  | ke_first (share : GroupElement)
  | ke_second (share : GroupElement)
  | smc_cipher (sid : Sid) (cipher : Ciphertext)
  deriving Repr, DecidableEq

/-- `Forw` 的业务消息。 -/
inductive ForwBody where
  | submit
      (sender_id receiver_id : MachineId)
      (payload : NetworkBody)
  | observe
      (sender_id receiver_id : MachineId)
      (payload : NetworkBody)
  | release
  | delivered
      (sender_id receiver_id : MachineId)
      (payload : NetworkBody)
  deriving Repr, DecidableEq

/-- `KE` 的业务消息。 -/
inductive KEBody where
  | init
  | confirm
  | observe_init
      (initiator_id responder_id : MachineId)
  | observe_confirm
  | release_init
  | release_confirm
  | key (shared_key : SharedKey)
  deriving Repr, DecidableEq

/-- `SMC` 的业务消息。 -/
inductive SMCBody where
  | send (sid : Sid) (plaintext : Plaintext)
  | observe (sid : Sid) (sender_id receiver_id : MachineId)
  | release (sid : Sid)
  | received (sid : Sid) (plaintext : Plaintext)
  deriving Repr, DecidableEq

/-- EasyUC case study 中各 functionality 共用的业务 payload。 -/
inductive SMCEasyUCPayload where
  | forw (body : ForwBody)
  | ke (body : KEBody)
  | smc (body : SMCBody)
  deriving Repr, DecidableEq

end LeanCryptoProtocols.UC.Functionality

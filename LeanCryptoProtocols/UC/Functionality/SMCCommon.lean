import LeanCryptoProtocols.UC.IdealWorld

/-!
# SMC EasyUC case study 的共享消息类型

本文件集中放置 EasyUC 的 secure message communication case study
需要共用的：

- 会话标识；
- 网络消息；
- `Forw` / `KE` / `SMC` 的业务消息；
- 在当前 ideal-world builder 下统一使用的 payload 类型。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC

/-- protocol session identifier。 -/
abbrev Sid : Type := Nat

/-- 某个 protocol session 内的子会话标识。 -/
abbrev Ssid : Type := Nat

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
  | ke_first (sid : Sid) (ssid : Ssid) (share : GroupElement)
  | ke_second (sid : Sid) (ssid : Ssid) (share : GroupElement)
  | smc_cipher (sid : Sid) (cipher : Ciphertext)
  deriving Repr, DecidableEq

/-- `Forw` 的业务消息。 -/
inductive ForwBody where
  | submit
      (sid : Sid)
      (sender_id receiver_id : MachineId)
      (payload : NetworkBody)
  | observe
      (sid : Sid)
      (sender_id receiver_id : MachineId)
      (payload : NetworkBody)
  | release (sid : Sid)
  | delivered
      (sid : Sid)
      (sender_id receiver_id : MachineId)
      (payload : NetworkBody)
  deriving Repr, DecidableEq

/-- `KE` 的业务消息。 -/
inductive KEBody where
  | init (sid : Sid) (ssid : Ssid)
  | confirm (sid : Sid) (ssid : Ssid)
  | observe_init
      (sid : Sid)
      (ssid : Ssid)
      (initiator_id responder_id : MachineId)
  | observe_confirm (sid : Sid) (ssid : Ssid)
  | release_init (sid : Sid) (ssid : Ssid)
  | release_confirm (sid : Sid) (ssid : Ssid)
  | key (sid : Sid) (ssid : Ssid) (shared_key : SharedKey)
  deriving Repr, DecidableEq

/-- `SMC` 的业务消息。 -/
inductive SMCBody where
  | send (sid : Sid) (plaintext : Plaintext)
  | observe (sid : Sid) (sender_id receiver_id : MachineId)
  | release (sid : Sid)
  | received (sid : Sid) (plaintext : Plaintext)
  deriving Repr, DecidableEq

/--
EasyUC case study 统一使用的 payload。

三个 functionality 都采用与 `IdealOT` 类似的包装方式：

- `plain`：environment / caller 与 dummy party 之间的业务消息；
- `to_functionality`：dummy party 转发给功能机；
- `from_functionality`：功能机返回给 dummy party。
-/
inductive SMCEasyUCPayload where
  | forw_plain (body : ForwBody)
  | forw_to_functionality (caller_source : Option MachineId) (body : ForwBody)
  | forw_from_functionality (destination : MachineId) (body : ForwBody)
  | ke_plain (body : KEBody)
  | ke_to_functionality (caller_source : Option MachineId) (body : KEBody)
  | ke_from_functionality (destination : MachineId) (body : KEBody)
  | smc_plain (body : SMCBody)
  | smc_to_functionality (caller_source : Option MachineId) (body : SMCBody)
  | smc_from_functionality (destination : MachineId) (body : SMCBody)
  deriving Repr, DecidableEq

end LeanCryptoProtocols.UC.Functionality

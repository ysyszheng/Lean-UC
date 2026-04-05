import LeanCryptoProtocols.UC.Machine

/-!
# Authenticated communication 的 channel machine

本文件给出一个最小的 authenticated communication channel machine。

它表达的语义很直接：

- sender 向 channel machine 发送一条消息；
- channel machine 原样把消息转发给指定 receiver；
- backdoor 端口保留给静态腐化 / transcript 暴露接口使用。

这里先提供可复用的 machine 组件与最基本的正确性化简定理。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- channel machine 的载荷：记录最终接收者以及消息体。 -/
structure ChannelPayload (Payload : Type u) where
  receiver : MachineId
  body : Payload
  deriving Repr, DecidableEq

/-- 构造一条发往 receiver 的 deliver 包。 -/
def mkDeliveredEnvelope
    {Payload : Type u}
    (chanId receiver : MachineId)
    (payload : Payload) :
    Envelope (ChannelPayload Payload) :=
  { sender := ⟨chanId, .subroutineOutput⟩
    receiver := ⟨receiver, .input⟩
    payload := ⟨receiver, payload⟩ }

/-- 最小的 authenticated communication channel program。 -/
noncomputable def channelProgram {Payload : Type u} (chanId : MachineId) :
    MachineProgram (ChannelPayload Payload) PUnit where
  LocalState := Unit
  init := ()
  step _ msg :=
    if msg.receiver = ⟨chanId, .input⟩ then
      PMF.pure
        { state := ()
          outgoing? := some (mkDeliveredEnvelope chanId msg.payload.receiver msg.payload.body) }
    else
      PMF.pure { state := (), outgoing? := none }
  output _ := PUnit.unit

/-- channel machine 的 communication set。 -/
def channelCommSet (chanId : MachineId) : Finset CommPort :=
  { ⟨chanId, .input⟩
  , ⟨chanId, .subroutineOutput⟩
  , ⟨chanId, .backdoor⟩
  }

/-- authenticated communication 对应的 channel machine。 -/
noncomputable def channelMachine {Payload : Type u} (chanId : MachineId) :
    Machine (ChannelPayload Payload) PUnit where
  id := chanId
  communicationSet := channelCommSet chanId
  program := channelProgram chanId

@[simp] theorem channelProgram_send_step
    {Payload : Type u} (chanId : MachineId)
    (msg : Envelope (ChannelPayload Payload))
    (hrecv : msg.receiver = ⟨chanId, .input⟩) :
    (channelProgram (Payload := Payload) chanId).step () msg =
      PMF.pure
        { state := ()
          outgoing? :=
            some (mkDeliveredEnvelope chanId msg.payload.receiver msg.payload.body) } := by
  simp [channelProgram, hrecv]

@[simp] theorem channelProgram_non_send_step
    {Payload : Type u} (chanId : MachineId)
    (msg : Envelope (ChannelPayload Payload))
    (hrecv : msg.receiver ≠ ⟨chanId, .input⟩) :
    (channelProgram (Payload := Payload) chanId).step () msg =
      PMF.pure { state := (), outgoing? := none } := by
  simp [channelProgram, hrecv]

end LeanCryptoProtocols.UC

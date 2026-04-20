import LeanCryptoProtocols.UC.IdealWorld

/-!
# UC-emulate / UC-realize

本文件建立在 `Machine.lean`、`Controller.lean` 与 `IdealWorld.lean` 之上，给出：

- UC-emulate；
- UC-realize。

这里固定采用 uniform 的 restricted model：不显式建模额外辅助输入，只保留安全参数 `n`。
-/

universe u

namespace LeanCryptoProtocols.UC

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
TODO: 需要限制S的corrupt set只包含F
-- TODO: functionality还可以和敌手通信。这个是在构造ExecutionSetup时通过给敌手的corruptionSet加入functionality的ID，后续调用runtime_communication_set动态实现吗
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

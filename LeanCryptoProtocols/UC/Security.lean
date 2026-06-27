import LeanCryptoProtocols.UC.IdealWorld

/-!
# UC-emulate / UC-realize

本文件建立在 `Machine.lean`、`Controller.lean` 与 `IdealWorld.lean` 之上，给出：

- UC-emulate；
- UC-realize。

这里固定采用 uniform 的 restricted model：不显式建模额外辅助输入，只保留安全参数 `n`。
-/

universe u wπ wφ wA wS wE

namespace LeanCryptoProtocols.UC

/-- 真实世界与理想世界在固定 `A,S,E,n` 下的执行差。 -/
noncomputable def exec_diff {Payload : Type u}
    {π : Protocol.{u, wπ} Payload}
    {φ : Protocol.{u, wφ} Payload}
    {A : Adversary.{u, wA} Payload}
    {S : Simulator.{u, wS} Payload}
    {E : Environment.{u, wE} Payload}
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
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  match level with
  | .perfect =>
      ∀ A : Adversary.{u, wA} Payload,
        ∃ S : Simulator.{u, wS} Payload,
        ∀ E : Environment.{u, wE} Payload,
          ∀ real_setup : ExecutionSetup π A E,
            ∀ ideal_setup : ExecutionSetup φ S E,
              real_setup.corrupted_parties = corruption_pattern →
                ideal_setup.corrupted_parties = corruption_pattern →
                  ∀ n, Controller.exec real_setup n = Controller.exec ideal_setup n
  | .statistical =>
      ∀ A : Adversary.{u, wA} Payload,
        ∃ S : Simulator.{u, wS} Payload,
        ∀ E : Environment.{u, wE} Payload,
          ∀ real_setup : ExecutionSetup π A E,
            ∀ ideal_setup : ExecutionSetup φ S E,
              real_setup.corrupted_parties = corruption_pattern →
                ideal_setup.corrupted_parties = corruption_pattern →
                  ∃ negl, Negligible negl ∧
                    ∀ n, exec_diff real_setup ideal_setup n ≤ negl n
  | .computational =>
      ∀ A : Adversary.{u, wA} Payload, PPT A →
        ∃ S : Simulator.{u, wS} Payload, PPT S ∧
          ∀ E : Environment.{u, wE} Payload, PPT E →
            ∀ real_setup : ExecutionSetup π A E,
              ∀ ideal_setup : ExecutionSetup φ S E,
                real_setup.corrupted_parties = corruption_pattern →
                  ideal_setup.corrupted_parties = corruption_pattern →
                    ∃ negl, Negligible negl ∧
                      ∀ n, exec_diff real_setup ideal_setup n ≤ negl n

/-- 常用简写。 -/
def UCEmulatesPerfect {Payload : Type u}
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  UCEmulatesAt.{u, wπ, wφ, 0, 0, 0} .perfect ∅ π φ

def UCEmulatesPerfectWithCorruption {Payload : Type u}
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  UCEmulatesAt.{u, wπ, wφ, 0, 0, 0} .perfect corruption_pattern π φ

def UCEmulatesStatistical {Payload : Type u}
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  UCEmulatesAt.{u, wπ, wφ, 0, 0, 0} .statistical ∅ π φ

def UCEmulatesStatisticalWithCorruption {Payload : Type u}
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  UCEmulatesAt.{u, wπ, wφ, 0, 0, 0} .statistical corruption_pattern π φ

def UCEmulatesComputational {Payload : Type u}
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  UCEmulatesAt.{u, wπ, wφ, 0, 0, 0} .computational ∅ π φ

def UCEmulatesComputationalWithCorruption {Payload : Type u}
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (φ : Protocol.{u, wφ} Payload) : Prop :=
  UCEmulatesAt.{u, wπ, wφ, 0, 0, 0} .computational corruption_pattern π φ

/--
UC-realize：协议 `π` UC-emulate 从 `F` 自动构造出的 ideal protocol。

与普通 `UCEmulatesAt` 不同，`UCRealizesAt` 知道理想协议来自某个
`IdealFunctionality`。

如果理想功能需要 simulator 的控制接口，该接口必须由功能机自己的
communication set 显式暴露为 backdoor/control port；controller 不再通过全局
集合额外赋予 simulator 控制能力。针对 party 的 corruption 消息只由固定
`ExecutionSetup.corrupted_parties` 控制，具体泄露和命令语义由 ideal functionality
的 program 决定。
-/
def UCRealizesAt {Payload : Type u}
    (level : SecurityLevel)
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCEmulatesAt.{u, wπ, 0, 0, 0, 0}
    level corruption_pattern π (mk_ideal_protocol f).protocol

/-- 常用简写。 -/
def UCRealizesPerfect {Payload : Type u}
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .perfect ∅ π f

def UCRealizesPerfectWithCorruption {Payload : Type u}
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .perfect corruption_pattern π f

def UCRealizesStatistical {Payload : Type u}
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .statistical ∅ π f

def UCRealizesStatisticalWithCorruption {Payload : Type u}
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .statistical corruption_pattern π f

def UCRealizesComputational {Payload : Type u}
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .computational ∅ π f

def UCRealizesComputationalWithCorruption {Payload : Type u}
    (corruption_pattern : Finset MachineId)
    (π : Protocol.{u, wπ} Payload)
    (f : IdealFunctionality Payload) : Prop :=
  UCRealizesAt .computational corruption_pattern π f

end LeanCryptoProtocols.UC

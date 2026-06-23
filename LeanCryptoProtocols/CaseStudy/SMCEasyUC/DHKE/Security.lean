import LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE.Model

/-!
# DHKE 子证明的安全里程碑

本文件证明 blueprint 中的 Theorem 19 形式：DH key exchange 的 concrete
DDH security。这里不引入 EasyUC 的 guard；合法执行条件由本项目的
`Machine`、`Protocol` 与 `ExecutionSetup` 结构约束表达。
-/

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

open LeanCryptoProtocols.Assumptions
open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality

/-! ## Setup-specific DDH reduction interface -/

/-- 真实 challenge execution 与 DDH real game 使用同一个输出分布。 -/
theorem ddh_game_eq_real_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    real_challenge_execution gen real_setup =
      ddh_game_one_of_real_setup gen real_setup := by
  rfl

/-- 随机 challenge execution 与 DDH random game 使用同一个输出分布。 -/
theorem ddh_game_eq_random_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    random_challenge_execution gen real_setup =
      ddh_game_two_of_real_setup gen real_setup := by
  rfl

/-- ideal challenge execution 与对应 DDH real game 使用同一个输出分布。 -/
theorem ddh_game_eq_real_ideal_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) :
    (fun n =>
      (ddh_real gen n).bind fun sample =>
        challenge_controller_output_of_ideal_setup gen ideal_setup sample n) =
      ddh_game_one_of_ideal_setup gen ideal_setup := by
  rfl

/-- ideal 随机 challenge execution 与对应 DDH random game 使用同一个输出分布。 -/
theorem ddh_game_eq_random_ideal_challenge_execution
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E) :
    random_ideal_challenge_execution gen ideal_setup =
      ddh_game_two_of_ideal_setup gen ideal_setup := by
  rfl

/--
Theorem 19 的 setup-specific 核心等式：
challenge-programmed controller 的执行差就是对应 DDH distinguisher 的优势。
-/
theorem concrete_ddh_security_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (n : ℕ) :
    challenge_exec_diff gen real_setup n ≤
      ddh_advantage gen (ddh_adversary_of_real_setup gen real_setup) n := by
  rfl

/--
由 controller 的通用 PPT 闭包接口得到 DDH reduction distinguisher 是 PPT。
-/
theorem ppt_ddh_adversary_of_real_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (hA : PPT A)
    (hE : PPT E) :
    PPT (α := Distinguisher DDHSample.{0})
      (ddh_adversary_of_real_setup gen real_setup) := by
  simpa [ddh_adversary_of_real_setup, challenge_controller_output_of_real_setup,
    ControllerExecution.exec, challenge_execution_of_real_setup] using
    (Controller.ppt_controller_distinguisher
      (setup := fun sample =>
        (challenge_execution_of_real_setup gen real_setup sample).setup)
      hA hE)

/--
Ideal-side DDH distinguisher 的 PPT 闭包义务。

Corrected challenge-ideal executions use `challenge_simulator gen sample A`, so
the adversary in the controller setup is parameterized by the DDH sample.  The
current generic `Controller.ppt_controller_distinguisher` interface only covers
a fixed adversary, hence this case is recorded as an explicit closure axiom
until the core PPT interface is generalized.
-/
axiom ppt_ddh_adversary_of_ideal_setup
    (gen : GroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E)
    (hA : PPT A)
    (hE : PPT E) :
    PPT (α := Distinguisher DDHSample.{0})
      (ddh_adversary_of_ideal_setup gen ideal_setup)

/--
DDH 假设推出 setup-specific challenge experiment 的 negligible 上界。
-/
theorem concrete_ddh_security_negligible_of_real_setup
    (gen : PPTGroupGenerator.{0})
    {A : Adversary SMCEasyUCPayload}
    {E : Environment SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen.run) A E)
    (hA : PPT A)
    (hE : PPT E)
    (hddh : ppt_ddh_assumption gen) :
    ∃ negl, Negligible negl ∧
      ∀ n, challenge_exec_diff gen.run real_setup n ≤ negl n := by
  dsimp [ppt_ddh_assumption, ddh_assumption, ComputationalIndist] at hddh
  have hred :=
    ppt_ddh_adversary_of_real_setup gen.run real_setup hA hE
  rcases hddh (ddh_adversary_of_real_setup gen.run real_setup) hred with
    ⟨negl, hnegl, hbound⟩
  refine ⟨negl, hnegl, ?_⟩
  intro n
  exact le_trans
    (concrete_ddh_security_of_real_setup gen.run real_setup n)
    (hbound n)

/-! ## Hybrid-chain obligations for the full UC theorem -/

/--
真实 witness 初始化的 controller execution 与 DDH-real challenge-programmed
controller execution 的逐 trace 匹配义务。

这是 `H0 = H1 = H2` 中唯一尚未由定义展开自动给出的部分：真实 party 保存
exponent witness，而 challenge party 只读取投影后的 DDH sample。该义务应由
controller-level bisimulation 证明，而不是作为密码学假设使用。核心层已经提供
`Controller.run_steps_output_eq_of_step_map`，这里后续需要补的是从真实 witness
state 到 challenge state 的投影，以及该投影与每一步 controller 调度交换。
-/
def RealWitnessTraceMatching (gen : GroupGenerator.{0}) : Prop :=
  ∀ {A : Adversary.{0, 0} SMCEasyUCPayload}
    {E : Environment.{0, 0} SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (witness : DDHRealWitness),
      real_controller_output_of_witness gen real_setup witness =
        challenge_controller_output_of_real_setup gen real_setup witness.to_sample

/--
DDH-random challenge-real execution 与 DDH-random challenge-ideal execution
的逐 trace 匹配义务。

这是 `H3 = H4`，也是目前最敏感的 proof obligation：它需要证明真实世界中
`A + Forw + DHKE parties` 的 trace 与理想世界中 `simulator A + dummy parties
+ IdealKE` 的 trace 可用 stuttering simulation 对齐。若只需要函数式投影，可直接
使用 `Controller.run_steps_output_eq_of_step_map`；若存在一侧多步 dummy 转发，则还
需要在该引理之上补一个 stuttering 版本。
-/
def RandomChallengeIdealTraceMatching (gen : GroupGenerator.{0}) : Prop :=
  ∀ {A : Adversary.{0, 0} SMCEasyUCPayload}
    {E : Environment.{0, 0} SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E)
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E),
      real_setup.corrupted_parties = ∅ →
        ideal_setup.corrupted_parties = ∅ →
          random_challenge_execution gen real_setup =
            random_ideal_challenge_execution gen ideal_setup

/--
标准 ideal-world sampler 通过 controller 的提升义务。

这是 H5 的 controller 部分：在已经证明 share/key 分离采样器联合分布一致后，
还要把该等价通过 `IdealKE`、`mk_ideal_protocol`、`ExecutionSetup` 与
`Controller.exec` 提升到环境输出分布。
-/
def IdealSamplerControllerLifting (gen : GroupGenerator.{0}) : Prop :=
  ∀ {A : Adversary.{0, 0} SMCEasyUCPayload}
    {E : Environment.{0, 0} SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E),
      random_ideal_challenge_execution gen ideal_setup =
        Controller.exec ideal_setup

/--
公共群 component-programmed ideal execution 到标准 ideal execution 的
controller lifting 义务。

`Model.lean` 已经证明 DDH-random challenge-ideal execution 等于该公共群
component execution；因此后续只需把公共群 component execution 与标准
`Controller.exec ideal_setup` 对齐。
-/
def PublicGroupIdealControllerLifting (gen : GroupGenerator.{0}) : Prop :=
  ∀ {A : Adversary.{0, 0} SMCEasyUCPayload}
    {E : Environment.{0, 0} SMCEasyUCPayload}
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen)).protocol
        (simulator gen A) E),
      public_group_ideal_component_execution gen ideal_setup =
        Controller.exec ideal_setup

/-- 公共群 component controller lifting 推出原 H5 controller lifting。 -/
theorem ideal_sampler_controller_lifting_of_public_group_controller_lifting
    (gen : GroupGenerator.{0})
    (h_public_controller : PublicGroupIdealControllerLifting gen) :
    IdealSamplerControllerLifting gen := by
  intro A E ideal_setup
  rw [random_ideal_challenge_execution_eq_public_group_component_execution]
  exact h_public_controller ideal_setup

/--
H5 的完整 proof obligation。

Corrected `IdealKE` 只采样 key material；simulator 自己采样或由 challenge
编程得到 fake DH public shares。因此 H5 必须显式包含两个部分：

1. 低层 share/key-separated sampler equivalence；
2. 把该采样等价提升到完整 controller execution。

这个结构避免把 DH transcript 塞进 `IdealKE` 的语义。
-/
structure IdealSamplerLifting (gen : GroupGenerator.{0}) : Prop where
  share_key_sampler : ShareKeySeparatedSamplerEquivalence gen
  controller_lifting : IdealSamplerControllerLifting gen

/--
用公共群参数 sampler 证明 H5 的标准入口。

`Model.lean` 已经证明公共群版本的 share/key 分离采样等于 DDH-random
projection。剩余工作是证明标准 ideal execution 的实际 sampler 确实等价于
该公共群版本，并把这个采样等价提升到 controller 输出。
-/
theorem ideal_sampler_lifting_of_public_group_sampler
    (gen : GroupGenerator.{0})
    (h_public :
      ∀ n,
        sample_standard_ideal_components gen n =
          sample_public_group_ideal_components gen n)
    (h_controller : IdealSamplerControllerLifting gen) :
    IdealSamplerLifting gen where
  share_key_sampler :=
    share_key_separated_sampler_equivalence_of_public_group_sampler gen h_public
  controller_lifting := h_controller

/--
更贴近 corrected H5 的 assembly：低层 sampler 使用公共群版本，controller 侧也
只需证明公共群 component execution 与标准 ideal execution 对齐。
-/
theorem ideal_sampler_lifting_of_public_group_obligations
    (gen : GroupGenerator.{0})
    (h_public_sampler :
      ∀ n,
        sample_standard_ideal_components gen n =
          sample_public_group_ideal_components gen n)
    (h_public_controller : PublicGroupIdealControllerLifting gen) :
    IdealSamplerLifting gen :=
  ideal_sampler_lifting_of_public_group_sampler gen h_public_sampler
    (ideal_sampler_controller_lifting_of_public_group_controller_lifting
      gen h_public_controller)

/--
Simulator wrapper 的 PPT 闭包。

本项目当前把 `PPT` 作为抽象复杂度接口；这个声明只记录“对 adversary 做有限
状态封装并黑盒调用其 `receive/resume` 保持 PPT”，不承担任何密码学安全结论。
-/
axiom ppt_simulator
    (gen : GroupGenerator.{0}) (A : Adversary.{0, 0} SMCEasyUCPayload) :
    PPT A → PPT (simulator gen A)

/-- `H0 = H2`：由真实 witness trace matching 推出真实执行等于 DDH-real challenge。 -/
theorem controller_exec_real_eq_real_challenge_execution
    (gen : GroupGenerator.{0})
    (htrace : RealWitnessTraceMatching gen)
    {A : Adversary.{0, 0} SMCEasyUCPayload}
    {E : Environment.{0, 0} SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen) A E) :
    Controller.exec real_setup =
      real_challenge_execution gen real_setup := by
  rw [controller_exec_real_eq_real_witness_controller_output gen real_setup]
  calc
    (fun n =>
        (ddh_real_witness gen n).bind fun witness =>
          real_controller_output_of_witness gen real_setup witness n)
        =
      (fun n =>
        (ddh_real_witness gen n).bind fun witness =>
          challenge_controller_output_of_real_setup gen real_setup witness.to_sample n) := by
        funext n
        simp [htrace real_setup]
    _ = real_challenge_execution gen real_setup := by
        exact real_witness_challenge_execution_eq_real_challenge_execution gen real_setup

/--
在三个 exact trace obligations 和 DDH 假设下，任意固定 real/ideal setup 的
`exec_diff` 有 negligible 上界。
-/
theorem exec_diff_bound_of_hybrid_obligations
    (gen : PPTGroupGenerator.{0})
    (h_real_trace : RealWitnessTraceMatching gen.run)
    (h_random_ideal : RandomChallengeIdealTraceMatching gen.run)
    (h_ideal_lift : IdealSamplerLifting gen.run)
    (hddh : ppt_ddh_assumption gen)
    {A : Adversary.{0, 0} SMCEasyUCPayload}
    {E : Environment.{0, 0} SMCEasyUCPayload}
    (real_setup : ExecutionSetup (real_protocol gen.run) A E)
    (ideal_setup :
      ExecutionSetup
        (mk_ideal_protocol (ideal_ke_functionality gen.run)).protocol
        (simulator gen.run A) E)
    (hA : PPT A)
    (hE : PPT E)
    (hreal_corr : real_setup.corrupted_parties = ∅)
    (hideal_corr : ideal_setup.corrupted_parties = ∅) :
    ∃ negl, Negligible negl ∧
      ∀ n, exec_diff real_setup ideal_setup n ≤ negl n := by
  rcases concrete_ddh_security_negligible_of_real_setup gen real_setup hA hE hddh with
    ⟨negl, hnegl, hbound⟩
  refine ⟨negl, hnegl, ?_⟩
  intro n
  have h_real_exec :
      Controller.exec real_setup =
        real_challenge_execution gen.run real_setup :=
    controller_exec_real_eq_real_challenge_execution gen.run h_real_trace real_setup
  have h_random :
      random_challenge_execution gen.run real_setup =
        random_ideal_challenge_execution gen.run ideal_setup :=
    h_random_ideal real_setup ideal_setup hreal_corr hideal_corr
  have h_ideal_exec :
      random_ideal_challenge_execution gen.run ideal_setup =
        Controller.exec ideal_setup :=
    h_ideal_lift.controller_lifting ideal_setup
  calc
    exec_diff real_setup ideal_setup n =
        challenge_exec_diff gen.run real_setup n := by
          simp [exec_diff, challenge_exec_diff, h_real_exec, ← h_ideal_exec,
            ← h_random]
    _ ≤ negl n := hbound n

/--
如果三个 exact trace obligations 成立，则得到显式展开的 DHKE computational
UC-realization theorem。

这个 theorem 明确暴露尚未完成的 controller trace proof obligations；它不是把这些
义务隐藏成安全假设，而是把最终 assembly 与待证 trace matching 分离开。
-/
theorem dhke_uc_realizes_ke_under_ddh_of_hybrid_obligations
    (gen : PPTGroupGenerator.{0})
    (h_real_trace : RealWitnessTraceMatching gen.run)
    (h_random_ideal : RandomChallengeIdealTraceMatching gen.run)
    (h_ideal_lift : IdealSamplerLifting gen.run)
    (hddh : ppt_ddh_assumption gen) :
    UCRealizesComputational
      (real_protocol gen.run)
      (ideal_ke_functionality gen.run) := by
  change
    ∀ A : Adversary.{0, 0} SMCEasyUCPayload, PPT A →
      ∃ S : Simulator.{0, 0} SMCEasyUCPayload, PPT S ∧
        ∀ E : Environment.{0, 0} SMCEasyUCPayload, PPT E →
          ∀ real_setup : ExecutionSetup (real_protocol gen.run) A E,
            ∀ ideal_setup :
              ExecutionSetup
                (mk_ideal_protocol (ideal_ke_functionality gen.run)).protocol
                S E,
                real_setup.corrupted_parties = ∅ →
                  ideal_setup.corrupted_parties = ∅ →
                    ∃ negl, Negligible negl ∧
                      ∀ n, exec_diff real_setup ideal_setup n ≤ negl n
  intro A hA
  refine ⟨simulator gen.run A, ppt_simulator gen.run A hA, ?_⟩
  intro E hE real_setup ideal_setup hreal_corr hideal_corr
  exact exec_diff_bound_of_hybrid_obligations gen h_real_trace h_random_ideal
    h_ideal_lift hddh real_setup ideal_setup hA hE hreal_corr hideal_corr

/--
Certificate convenience wrapper：只把显式 UC theorem 包装回 `uc_realizes`。
-/
theorem uc_realizes_theorem_of_hybrid_obligations
    (gen : PPTGroupGenerator.{0})
    (h_real_trace : RealWitnessTraceMatching gen.run)
    (h_random_ideal : RandomChallengeIdealTraceMatching gen.run)
    (h_ideal_lift : IdealSamplerLifting gen.run) :
    uc_realizes gen := by
  intro hddh
  exact dhke_uc_realizes_ke_under_ddh_of_hybrid_obligations
    gen h_real_trace h_random_ideal h_ideal_lift hddh

end LeanCryptoProtocols.CaseStudy.SMCEasyUC.DHKE

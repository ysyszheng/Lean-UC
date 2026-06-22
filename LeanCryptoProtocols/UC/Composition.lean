import LeanCryptoProtocols.UC.Security

/-!
# 基于执行约化的 universal composition

本文件删除旧的 `ProtocolShape` / `ExecutableProtocol` 兼容层，
改为直接对当前主线的

- `Protocol`
- `ExecutionSetup`
- `Controller.exec`

给出一个适合 case study 使用的组合接口。

这里的核心思路是：

- 组合上下文 `ctx` 负责说明如何把一个子协议 `σ` 插入宿主上下文；
- 同时给出 adversary / simulator / environment 的投影与提升；
- 以及把宿主执行约化回子协议执行的 setup 级映射；
- `universal_composition` 再在这些约化事实上 lift `UCEmulatesAt`。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- 基于当前 controller 语义的组合上下文。 -/
structure CompositionContext (Payload : Type u) where
  plug : Protocol Payload → Protocol Payload
  project_adversary : Adversary.{u, 0} Payload → Adversary.{u, 0} Payload
  project_environment : Environment.{u, 0} Payload → Environment.{u, 0} Payload
  lift_simulator : Simulator.{u, 0} Payload → Simulator.{u, 0} Payload
  real_setup_of :
    ∀ {σ : Protocol Payload} {A : Adversary.{u, 0} Payload}
      {E : Environment.{u, 0} Payload},
      ExecutionSetup (plug σ) A E →
        ExecutionSetup σ (project_adversary A) (project_environment E)
  real_setup_corruption :
    ∀ {σ : Protocol Payload} {A : Adversary.{u, 0} Payload}
      {E : Environment.{u, 0} Payload}
      (setup : ExecutionSetup (plug σ) A E),
      (real_setup_of setup).corrupted_parties = setup.corrupted_parties
  ideal_setup_of :
    ∀ {σ : Protocol Payload} {S : Simulator.{u, 0} Payload}
      {E : Environment.{u, 0} Payload},
      ExecutionSetup (plug σ) (lift_simulator S) E →
        ExecutionSetup σ S (project_environment E)
  ideal_setup_corruption :
    ∀ {σ : Protocol Payload} {S : Simulator.{u, 0} Payload}
      {E : Environment.{u, 0} Payload}
      (setup : ExecutionSetup (plug σ) (lift_simulator S) E),
      (ideal_setup_of setup).corrupted_parties = setup.corrupted_parties
  adv_closed :
    ∀ A : Adversary.{u, 0} Payload, PPT A → PPT (project_adversary A)
  env_closed :
    ∀ E : Environment.{u, 0} Payload, PPT E → PPT (project_environment E)
  sim_closed :
    ∀ S : Simulator.{u, 0} Payload, PPT S → PPT (lift_simulator S)
  real_reduction :
    ∀ {σ : Protocol Payload} {A : Adversary.{u, 0} Payload}
      {E : Environment.{u, 0} Payload}
      (setup : ExecutionSetup (plug σ) A E) (n : ℕ),
      Controller.exec setup n =
        Controller.exec (real_setup_of setup) n
  ideal_reduction :
    ∀ {σ : Protocol Payload} {S : Simulator.{u, 0} Payload}
      {E : Environment.{u, 0} Payload}
      (setup : ExecutionSetup (plug σ) (lift_simulator S) E) (n : ℕ),
      Controller.exec setup n =
        Controller.exec (ideal_setup_of setup) n

/--
Universal composition 的当前主线版本。

如果子协议 `ρ` UC-emulate `φ`，并且组合上下文 `ctx` 给出了宿主执行到子协议执行的
精确约化，那么把 `ρ` 插入上下文后得到的协议，也 UC-emulate 把 `φ` 插入后的协议。
-/
theorem universal_composition {Payload : Type u}
    (level : SecurityLevel)
    (corruption_pattern : Finset MachineId)
    (ctx : CompositionContext Payload)
    (ρ φ : Protocol Payload)
    (hemu : UCEmulatesAt.{u, 0, 0, 0, 0, 0} level corruption_pattern ρ φ) :
    UCEmulatesAt.{u, 0, 0, 0, 0, 0}
      level corruption_pattern (ctx.plug ρ) (ctx.plug φ) := by
  cases level with
  | perfect =>
      intro A
      obtain ⟨S, hsim⟩ := hemu (ctx.project_adversary A)
      refine ⟨ctx.lift_simulator S, ?_⟩
      intro E real_setup ideal_setup h_real_corr h_ideal_corr n
      have h_real_projected :
          (ctx.real_setup_of real_setup).corrupted_parties = corruption_pattern := by
        rw [ctx.real_setup_corruption real_setup, h_real_corr]
      have h_ideal_projected :
          (ctx.ideal_setup_of ideal_setup).corrupted_parties = corruption_pattern := by
        rw [ctx.ideal_setup_corruption ideal_setup, h_ideal_corr]
      have hbase :=
        hsim (ctx.project_environment E) (ctx.real_setup_of real_setup)
          (ctx.ideal_setup_of ideal_setup) h_real_projected h_ideal_projected n
      calc
        Controller.exec real_setup n =
            Controller.exec (ctx.real_setup_of real_setup) n := by
              exact ctx.real_reduction real_setup n
        _ = Controller.exec (ctx.ideal_setup_of ideal_setup) n := hbase
        _ = Controller.exec ideal_setup n := by
              symm
              exact ctx.ideal_reduction ideal_setup n
  | statistical =>
      intro A
      obtain ⟨S, hsim⟩ := hemu (ctx.project_adversary A)
      refine ⟨ctx.lift_simulator S, ?_⟩
      intro E real_setup ideal_setup h_real_corr h_ideal_corr
      have h_real_projected :
          (ctx.real_setup_of real_setup).corrupted_parties = corruption_pattern := by
        rw [ctx.real_setup_corruption real_setup, h_real_corr]
      have h_ideal_projected :
          (ctx.ideal_setup_of ideal_setup).corrupted_parties = corruption_pattern := by
        rw [ctx.ideal_setup_corruption ideal_setup, h_ideal_corr]
      obtain ⟨negl, hnegl, hbound⟩ :=
        hsim (ctx.project_environment E) (ctx.real_setup_of real_setup)
          (ctx.ideal_setup_of ideal_setup) h_real_projected h_ideal_projected
      refine ⟨negl, hnegl, ?_⟩
      intro n
      simpa [exec_diff, ctx.real_reduction real_setup n, ctx.ideal_reduction ideal_setup n]
        using hbound n
  | computational =>
      intro A hA
      obtain ⟨S, hS, hsim⟩ :=
        hemu (ctx.project_adversary A) (ctx.adv_closed A hA)
      refine ⟨ctx.lift_simulator S, ctx.sim_closed S hS, ?_⟩
      intro E hE real_setup ideal_setup h_real_corr h_ideal_corr
      have h_real_projected :
          (ctx.real_setup_of real_setup).corrupted_parties = corruption_pattern := by
        rw [ctx.real_setup_corruption real_setup, h_real_corr]
      have h_ideal_projected :
          (ctx.ideal_setup_of ideal_setup).corrupted_parties = corruption_pattern := by
        rw [ctx.ideal_setup_corruption ideal_setup, h_ideal_corr]
      obtain ⟨negl, hnegl, hbound⟩ :=
        hsim (ctx.project_environment E) (ctx.env_closed E hE)
          (ctx.real_setup_of real_setup) (ctx.ideal_setup_of ideal_setup)
          h_real_projected h_ideal_projected
      refine ⟨negl, hnegl, ?_⟩
      intro n
      simpa [exec_diff, ctx.real_reduction real_setup n, ctx.ideal_reduction ideal_setup n]
        using hbound n

end LeanCryptoProtocols.UC

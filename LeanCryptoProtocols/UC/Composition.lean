import LeanCryptoProtocols.UC.Security

/-!
# compatible / identity-compatible / universal composition

本文件给出 Section 2 风格的 subroutine 组合接口，以及 universal composition theorem。

这里采用一个对 Lean 友好的组织方式：

- `ProtocolShape` 负责记录结构性信息；
- `CompositionContext` 负责记录“把某个 subroutine 插入到宿主协议后，执行如何约化到被插入协议”的语义接口；
- `UniversalComposition` 在这个接口之上严格证明。
-/

universe u v

namespace LeanCryptoProtocols.UC

/-- 带根 identity 的 subroutine protocol。 -/
structure SubroutineProtocol (Label : Type u) (Payload : Type v) (Aux : Type u)
    extends ExecutableProtocol Label Payload Aux where
  rootId : MachineId
  rooted : ProtocolShape.RootedAt toProtocolShape rootId

/-- 语义上的 subroutine replacement 上下文。 -/
structure CompositionContext (Label : Type u) (Payload : Type v) (Aux : Type u) where
  host : ProtocolShape Label Payload
  slotId : MachineId
  plug :
    SubroutineProtocol Label Payload Aux →
    ExecutableProtocol Label Payload Aux
  projectAdv :
    Adversary Label Payload →
    Adversary Label Payload
  projectEnv :
    Environment Label Payload Aux →
    Environment Label Payload Aux
  liftSim :
    Simulator Label Payload →
    Simulator Label Payload
  usesSlot : host.UsesSubroutine slotId

/-- 结构性 compatible：替换进去的 subroutine 必须根植于目标槽位。 -/
def Compatible {Label : Type u} {Payload : Type v} {Aux : Type u}
    (ctx : CompositionContext Label Payload Aux)
    (σ : SubroutineProtocol Label Payload Aux) : Prop :=
  σ.rootId = ctx.slotId

/--
identity-compatible：替换操作不改变槽位外的 identity。

这里用一个适合当前框架的最小版本：`plug σ` 至少保留宿主协议里所有非槽位子树上的 identity。
-/
def IdentityCompatible {Label : Type u} {Payload : Type v} {Aux : Type u}
    (ctx : CompositionContext Label Payload Aux)
    (σ : SubroutineProtocol Label Payload Aux) : Prop :=
  ∀ mid, mid ∈ machineIds ctx.host.machines →
    ¬ IsProperPrefix ctx.slotId mid →
    mid ∈ machineIds (ctx.plug σ).machines

/-- 把某个 subroutine protocol 插入宿主上下文。 -/
def ReplaceSubroutine {Label : Type u} {Payload : Type v} {Aux : Type u}
    (ctx : CompositionContext Label Payload Aux)
    (σ : SubroutineProtocol Label Payload Aux) :
    ExecutableProtocol Label Payload Aux :=
  ctx.plug σ

/--
组合语义的关键约化性质。

这两个等式表达的是：宿主协议在插入 subroutine 后，环境真正看到的执行
可以投影回被插入 subroutine 的执行。
-/
structure CompositionSound {Label : Type u} {Payload : Type v} {Aux : Type u}
    (ctx : CompositionContext Label Payload Aux)
    (PPTAdv : Adversary Label Payload → Prop)
    (PPTEnv : Environment Label Payload Aux → Prop) : Prop where
  adv_closed : ∀ A, PPTAdv A → PPTAdv (ctx.projectAdv A)
  env_closed : ∀ E, PPTEnv E → PPTEnv (ctx.projectEnv E)
  sim_closed : ∀ S, PPTAdv S → PPTAdv (ctx.liftSim S)
  real_reduction :
    ∀ (σ : SubroutineProtocol Label Payload Aux) (A : Adversary Label Payload)
      (E : Environment Label Payload Aux) (z : Aux) (n : ℕ),
      (ctx.plug σ).exec A E z n = σ.exec (ctx.projectAdv A) (ctx.projectEnv E) z n
  ideal_reduction :
    ∀ (σ : SubroutineProtocol Label Payload Aux) (S : Simulator Label Payload)
      (E : Environment Label Payload Aux) (z : Aux) (n : ℕ),
      (ctx.plug σ).exec (ctx.liftSim S) E z n = σ.exec S (ctx.projectEnv E) z n

/--
universal composition theorem。

如果 `ρ` UC-emulate `φ`，那么把 `ρ` 替换进宿主协议所得的整体协议，
也 UC-emulate 把 `φ` 替换进去后的整体协议。
-/
theorem universalComposition {Label : Type u} {Payload : Type v} {Aux : Type u}
    (level : SecurityLevel)
    (ε : ℕ → ℝ)
    (PPTAdv : Adversary Label Payload → Prop)
    (PPTEnv : Environment Label Payload Aux → Prop)
    (ctx : CompositionContext Label Payload Aux)
    (ρ φ : SubroutineProtocol Label Payload Aux)
    (_hCompatR : Compatible ctx ρ)
    (_hCompatF : Compatible ctx φ)
    (_hIdR : IdentityCompatible ctx ρ)
    (_hIdF : IdentityCompatible ctx φ)
    (hsound : CompositionSound ctx PPTAdv PPTEnv)
    (hemu : UCEmulatesAt level ε PPTAdv PPTEnv ρ.toExecutableProtocol φ.toExecutableProtocol) :
    UCEmulatesAt level ε PPTAdv PPTEnv
      (ReplaceSubroutine ctx ρ)
      (ReplaceSubroutine ctx φ) := by
  intro A hA
  obtain ⟨S, hS, hsim⟩ := hemu (ctx.projectAdv A) (hsound.adv_closed A hA)
  refine ⟨ctx.liftSim S, hsound.sim_closed S hS, ?_⟩
  intro E hE
  have hbase := hsim (ctx.projectEnv E) (hsound.env_closed E hE)
  have hreal :
      ExecEnsemble (ReplaceSubroutine ctx ρ) A E =
        ExecEnsemble ρ.toExecutableProtocol (ctx.projectAdv A) (ctx.projectEnv E) := by
    funext z n
    simp [ExecEnsemble, ReplaceSubroutine, hsound.real_reduction]
  have hideal :
      ExecEnsemble (ReplaceSubroutine ctx φ) (ctx.liftSim S) E =
        ExecEnsemble φ.toExecutableProtocol S (ctx.projectEnv E) := by
    funext z n
    simp [ExecEnsemble, ReplaceSubroutine, hsound.ideal_reduction]
  cases level with
  | perfect =>
      intro z n
      rw [hreal, hideal]
      exact hbase z n
  | statistical =>
      intro z n
      rw [hreal, hideal]
      exact hbase z n
  | computational =>
      intro z
      rw [hreal, hideal]
      exact hbase z

end LeanCryptoProtocols.UC

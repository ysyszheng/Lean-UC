import LeanCryptoProtocols.UC.Security

/-!
# compatible / identity-compatible / universal composition

本文件给出 Section 2 风格的 subroutine 组合接口，以及 universal composition theorem。

这里采用一个对 Lean 友好的组织方式：

- `ProtocolShape` 负责记录结构性信息；
- `CompositionContext` 负责记录“把某个 subroutine 插入到宿主协议某个 slot identity 后，
  执行如何约化到被插入协议”的语义接口；
- `UniversalComposition` 在这个接口之上严格证明。
-/

universe u

namespace LeanCryptoProtocols.UC

/-- subroutine protocol：记录其可执行语义以及对外入口 identity。 -/
structure SubroutineProtocol (Payload : Type u)
    extends ExecutableProtocol Payload where
  entryId : MachineId
  hasEntry : toProtocolShape.HasMachineId entryId

/-- 一个 slot 对外暴露的 communication interface。 -/
structure SlotInterface where
  communicationSet : Finset CommPort

/-- 子协议是否在给定 slot identity 上实现。 -/
def ImplementsAt {Payload : Type u}
    (σ : SubroutineProtocol Payload) (slotId : MachineId) : Prop :=
  σ.entryId = slotId

/-- 语义上的 subroutine replacement 上下文。 -/
structure CompositionContext (Payload : Type u) where
  host : ProtocolShape Payload
  slotId : MachineId
  slotInterface : SlotInterface
  plug :
    SubroutineProtocol Payload →
    ExecutableProtocol Payload
  projectAdv :
    Adversary Payload →
    Adversary Payload
  projectEnv :
    Environment Payload →
    Environment Payload
  liftSim :
    Simulator Payload →
    Simulator Payload
  usesSlot : host.UsesSubroutine slotId

/-- 结构性 compatible：子协议入口身份与 slot 一致，且入口 machine 的外部接口一致。 -/
def Compatible {Payload : Type u}
    (ctx : CompositionContext Payload)
    (σ : SubroutineProtocol Payload) : Prop :=
  ImplementsAt σ ctx.slotId ∧
  ∃ m ∈ σ.toProtocolShape.machines,
    AnyMachine.id m = σ.entryId ∧
    m.2.communicationSet = ctx.slotInterface.communicationSet

/--
identity-compatible：替换操作不改变槽位外的 identity。

这里用一个适合当前框架的最小版本：

- 宿主协议里所有槽位外的 identity 在替换后保持不变；
- 插入后的协议仍包含 `slotId`。
-/
def IdentityCompatible {Payload : Type u}
    (ctx : CompositionContext Payload)
    (σ : SubroutineProtocol Payload) : Prop :=
  (∀ mid, mid ≠ ctx.slotId →
    (mid ∈ machineIds ctx.host.machines ↔
      mid ∈ machineIds (ctx.plug σ).machines)) ∧
  ctx.slotId ∈ machineIds (ctx.plug σ).machines

/-- 把某个 subroutine protocol 插入宿主上下文。 -/
def ReplaceSubroutine {Payload : Type u}
    (ctx : CompositionContext Payload)
    (σ : SubroutineProtocol Payload) :
    ExecutableProtocol Payload :=
  ctx.plug σ

/--
组合语义的关键约化性质。

这两个等式表达的是：宿主协议在插入 subroutine 后，环境真正看到的执行
可以投影回被插入 subroutine 的执行。
-/
structure CompositionSound {Payload : Type u}
    (ctx : CompositionContext Payload) : Prop where
  adv_closed : ∀ A, PPT A → PPT (ctx.projectAdv A)
  env_closed : ∀ E, PPT E → PPT (ctx.projectEnv E)
  sim_closed : ∀ S, PPT S → PPT (ctx.liftSim S)
  real_reduction :
    ∀ (σ : SubroutineProtocol Payload) (A : Adversary Payload)
      (E : Environment Payload) (n : ℕ),
      (ctx.plug σ).exec A E n = σ.exec (ctx.projectAdv A) (ctx.projectEnv E) n
  ideal_reduction :
    ∀ (σ : SubroutineProtocol Payload) (S : Simulator Payload)
      (E : Environment Payload) (n : ℕ),
      (ctx.plug σ).exec (ctx.liftSim S) E n = σ.exec S (ctx.projectEnv E) n

/--
universal composition theorem。

如果 `ρ` UC-emulate `φ`，那么把 `ρ` 替换进宿主协议所得的整体协议，
也 UC-emulate 把 `φ` 替换进去后的整体协议。
-/
theorem universalComposition {Payload : Type u}
    (level : SecurityLevel)
    (ctx : CompositionContext Payload)
    (ρ φ : SubroutineProtocol Payload)
    (_hCompatR : Compatible ctx ρ)
    (_hCompatF : Compatible ctx φ)
    (_hIdR : IdentityCompatible ctx ρ)
    (_hIdF : IdentityCompatible ctx φ)
    (hsound : CompositionSound ctx)
    (hemu : UCEmulatesAt level ρ.toExecutableProtocol φ.toExecutableProtocol) :
    UCEmulatesAt level
      (ReplaceSubroutine ctx ρ)
      (ReplaceSubroutine ctx φ) := by
  cases level with
  | perfect =>
      intro A
      obtain ⟨S, hsim⟩ := hemu (ctx.projectAdv A)
      refine ⟨ctx.liftSim S, ?_⟩
      intro E n
      have hbase := hsim (ctx.projectEnv E) n
      calc
        (ReplaceSubroutine ctx ρ).exec A E n =
            ρ.exec (ctx.projectAdv A) (ctx.projectEnv E) n := by
          simpa [ReplaceSubroutine] using hsound.real_reduction ρ A E n
        _ = φ.exec S (ctx.projectEnv E) n := hbase
        _ = (ReplaceSubroutine ctx φ).exec (ctx.liftSim S) E n := by
          symm
          simpa [ReplaceSubroutine] using hsound.ideal_reduction φ S E n
  | statistical =>
      intro A
      obtain ⟨S, hsim⟩ := hemu (ctx.projectAdv A)
      refine ⟨ctx.liftSim S, ?_⟩
      intro E
      obtain ⟨negl, hnegl, hbound⟩ := hsim (ctx.projectEnv E)
      refine ⟨negl, hnegl, ?_⟩
      intro n
      simp only [ExecDiff, ReplaceSubroutine]
      rw [hsound.real_reduction ρ A E n, hsound.ideal_reduction φ S E n]
      exact hbound n
  | computational =>
      intro A hA
      obtain ⟨S, hS, hsim⟩ := hemu (ctx.projectAdv A) (hsound.adv_closed A hA)
      refine ⟨ctx.liftSim S, hsound.sim_closed S hS, ?_⟩
      intro E hE
      obtain ⟨negl, hnegl, hbound⟩ := hsim (ctx.projectEnv E) (hsound.env_closed E hE)
      refine ⟨negl, hnegl, ?_⟩
      intro n
      simp only [ExecDiff, ReplaceSubroutine]
      rw [hsound.real_reduction ρ A E n, hsound.ideal_reduction φ S E n]
      exact hbound n

end LeanCryptoProtocols.UC

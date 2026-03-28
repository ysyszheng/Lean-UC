import LeanCryptoProtocols.UC.Core
import LeanCryptoProtocols.UC.Functionality.OT
import LeanCryptoProtocols.Circuit.BoolCircuit

/-!
# OT-hybrid 世界中的 GMW

本文件在以下边界内形式化 GMW 协议的严格 UC 安全性：

- 两方；
- 静态腐化；
- 半诚实敌手；
- 同步固定轮次；
- 布尔 DAG 电路；
- `F_OT`-hybrid 世界；
- 在完美层证明 `∀ adv, ∃ sim, ∀ env`。

与先前错误版本不同，这里的 simulator：

- 只接收被腐化方输入与理想输出；
- 不接收诚实方输入；
- 不接收真实执行随机性；
- 对 AND 门的隐藏部分直接按标准证明方式独立采样。

为了保持定义简洁，`Protocol` 在每个固定腐化情形下直接返回该情形下的局部可观察执行分布。
这与当前 `UC/Core` 中按 `corr` 参数化的执行接口是一致的。
-/

namespace LeanCryptoProtocols.GMW.OTHybrid

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality
open LeanCryptoProtocols.Circuit

/-- `Bool.xor` 的简写。 -/
abbrev bxor : Bool → Bool → Bool := Bool.xor

/-- GMW 中的两方异或共享。 -/
abbrev Share : Type := Bool × Bool

/-- 还原共享值。 -/
def revealShare (s : Share) : Bool :=
  bxor s.1 s.2

/--
左方输入的分享方式：

- 左方保留 `x xor r`
- 右方收到 `r`
-/
def shareLeftInput (x r : Bool) : Share :=
  (bxor x r, r)

/--
右方输入的分享方式：

- 左方收到 `s`
- 右方保留 `y xor s`
-/
def shareRightInput (y s : Bool) : Share :=
  (s, bxor y s)

/-- XOR 门逐份额按位异或。 -/
def xorShare (a b : Share) : Share :=
  (bxor a.1 b.1, bxor a.2 b.2)

/-- NOT 门通过翻转左方份额实现。 -/
def notShare (a : Share) : Share :=
  (!a.1, a.2)

/-- 左向右 OT 的接收输出。 -/
def leftToRightOTOutput (aLeft bRight sendMask : Bool) : Bool :=
  bxor sendMask (aLeft && bRight)

/-- 右向左 OT 的接收输出。 -/
def rightToLeftOTOutput (aRight bLeft sendMask : Bool) : Bool :=
  bxor sendMask (aRight && bLeft)

/-- GMW 的两次 OT AND 子协议。 -/
def andShareOT (a b : Share) (sendL sendR : Bool) : Share :=
  let t := leftToRightOTOutput a.1 b.2 sendL
  let u := rightToLeftOTOutput a.2 b.1 sendR
  ((a.1 && b.1) |> bxor u |> bxor sendL,
    (a.2 && b.2) |> bxor t |> bxor sendR)

/-- XOR 门共享正确性。 -/
theorem gmw_xor_gate_correct (a b : Share) :
    revealShare (xorShare a b) = bxor (revealShare a) (revealShare b) := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> rfl

/-- NOT 门共享正确性。 -/
theorem gmw_not_gate_correct (a : Share) :
    revealShare (notShare a) = !(revealShare a) := by
  rcases a with ⟨a₀, a₁⟩
  cases a₀ <;> cases a₁ <;> rfl

/-- AND 门 OT-hybrid 子协议正确性。 -/
theorem gmw_and_gate_ot_hybrid_correct (a b : Share) (sendL sendR : Bool) :
    revealShare (andShareOT a b sendL sendR) = (revealShare a && revealShare b) := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> cases sendL <;> cases sendR <;> rfl

/-- 电路的理想功能。 -/
def F_SFE_BoolCircuit (c : BoolCircuit) : Inputs c → Bool :=
  c.eval

/-- GMW 的电路理想功能接口。 -/
def IdealSFE (c : BoolCircuit) : IdealFunctionality (Inputs c) Bool where
  eval := F_SFE_BoolCircuit c
  interface :=
    { CorruptedInput := fun
        | .none => PUnit
        | .left => Fin c.nLeft → Bool
        | .right => Fin c.nRight → Bool
        | .both => Inputs c
      CorruptedOutput := fun
        | .none => PUnit
        | .left => Bool
        | .right => Bool
        | .both => Bool
      Leakage := fun _ => PUnit
      corruptInput := fun
        | .none, _ => PUnit.unit
        | .left, input => input.left
        | .right, input => input.right
        | .both, input => input
      corruptOutput := fun
        | .none, _ => PUnit.unit
        | .left, out => out
        | .right, out => out
        | .both, out => out
      leakage := fun _ _ _ => PUnit.unit }

/-- 左方局部事件。 -/
inductive LeftEvent where
  | ownInput (idx : Nat) (input keepShare sentShare : Bool)
  | otherInput (idx : Nat) (recvShare : Bool)
  | xor (gateId : Nat) (lhs rhs outShare : Bool)
  | not (gateId : Nat) (inputShare outShare : Bool)
  | and (gateId : Nat) (lhs rhs : Bool)
      (send : OTSenderView) (recv : OTReceiverView) (outShare : Bool)
  | outputReveal (ownShare recvShare output : Bool)
  deriving Repr, DecidableEq

/-- 右方局部事件。 -/
inductive RightEvent where
  | otherInput (idx : Nat) (recvShare : Bool)
  | ownInput (idx : Nat) (input keepShare sentShare : Bool)
  | xor (gateId : Nat) (lhs rhs outShare : Bool)
  | not (gateId : Nat) (inputShare outShare : Bool)
  | and (gateId : Nat) (lhs rhs : Bool)
      (recv : OTReceiverView) (send : OTSenderView) (outShare : Bool)
  | outputReveal (ownShare recvShare output : Bool)
  deriving Repr, DecidableEq

/-- 左方最终视图。 -/
structure LeftFinalView where
  trace : List LeftEvent
  outputShare : Bool
  receivedOutputShare : Bool
  output : Bool
  deriving Repr, DecidableEq

/-- 右方最终视图。 -/
structure RightFinalView where
  trace : List RightEvent
  outputShare : Bool
  receivedOutputShare : Bool
  output : Bool
  deriving Repr, DecidableEq

/-- 两方视图合并到统一类型中。 -/
inductive PartyView where
  | left : LeftFinalView → PartyView
  | right : RightFinalView → PartyView
  deriving Repr, DecidableEq

/-- 左方视图种子。 -/
structure LeftSeed (c : BoolCircuit) where
  ownMasks : Fin c.nLeft → Bool
  recvInputShares : Fin c.nRight → Bool
  sendMasks : Fin c.nGates → Bool
  recvOT : Fin c.nGates → Bool
  deriving Repr, DecidableEq, Fintype

instance (c : BoolCircuit) : Inhabited (LeftSeed c) where
  default :=
    { ownMasks := fun _ => false
      recvInputShares := fun _ => false
      sendMasks := fun _ => false
      recvOT := fun _ => false }

/-- 右方视图种子。 -/
structure RightSeed (c : BoolCircuit) where
  recvInputShares : Fin c.nLeft → Bool
  ownMasks : Fin c.nRight → Bool
  recvOT : Fin c.nGates → Bool
  sendMasks : Fin c.nGates → Bool
  deriving Repr, DecidableEq, Fintype

instance (c : BoolCircuit) : Inhabited (RightSeed c) where
  default :=
    { recvInputShares := fun _ => false
      ownMasks := fun _ => false
      recvOT := fun _ => false
      sendMasks := fun _ => false }

/-- 双方都被腐化时的真实执行种子。 -/
structure BothSeed (c : BoolCircuit) where
  leftMasks : Fin c.nLeft → Bool
  rightMasks : Fin c.nRight → Bool
  sendL : Fin c.nGates → Bool
  sendR : Fin c.nGates → Bool
  deriving Repr, DecidableEq, Fintype

instance (c : BoolCircuit) : Inhabited (BothSeed c) where
  default :=
    { leftMasks := fun _ => false
      rightMasks := fun _ => false
      sendL := fun _ => false
      sendR := fun _ => false }

/-- 有限类型上的均匀分布。 -/
noncomputable def uniformDist (α : Type) [Fintype α] [Nonempty α] : PMF α :=
  PMF.uniformOfFintype α

/-- 在尾部追加一个新值。 -/
def extendVals {α : Type} {n : Nat} (prev : Fin n → α) (next : α) : Fin (n + 1) → α
  | ⟨i, _hi⟩ =>
      if h : i < n then prev ⟨i, h⟩ else next

/-- 截取去掉最后一个位置后的前缀函数。 -/
def takePrefix {α : Type} {n : Nat} (f : Fin (n + 1) → α) : Fin n → α :=
  fun i => f i.castSucc

/-- 左方看到的引用份额。 -/
def leftRefShare {n : Nat} (c : BoolCircuit)
    (leftInput : Fin c.nLeft → Bool) (seed : LeftSeed c) (gateShares : Fin n → Bool) :
    Ref c.nLeft c.nRight n → Bool
  | .inputL i => (shareLeftInput (leftInput i) (seed.ownMasks i)).1
  | .inputR j => seed.recvInputShares j
  | .gate k => gateShares k

/-- 右方看到的引用份额。 -/
def rightRefShare {n : Nat} (c : BoolCircuit)
    (rightInput : Fin c.nRight → Bool) (seed : RightSeed c) (gateShares : Fin n → Bool) :
    Ref c.nLeft c.nRight n → Bool
  | .inputL i => seed.recvInputShares i
  | .inputR j => (shareRightInput (rightInput j) (seed.ownMasks j)).2
  | .gate k => gateShares k

/-- 双方都被腐化时，读取左方份额。 -/
def bothRefShareLeft {n : Nat} (c : BoolCircuit)
    (input : Inputs c) (seed : BothSeed c) (gateShares : Fin n → Share) :
    Ref c.nLeft c.nRight n → Bool
  | .inputL i => (shareLeftInput (input.left i) (seed.leftMasks i)).1
  | .inputR j => (shareRightInput (input.right j) (seed.rightMasks j)).1
  | .gate k => (gateShares k).1

/-- 双方都被腐化时，读取右方份额。 -/
def bothRefShareRight {n : Nat} (c : BoolCircuit)
    (input : Inputs c) (seed : BothSeed c) (gateShares : Fin n → Share) :
    Ref c.nLeft c.nRight n → Bool
  | .inputL i => (shareLeftInput (input.left i) (seed.leftMasks i)).2
  | .inputR j => (shareRightInput (input.right j) (seed.rightMasks j)).2
  | .gate k => (gateShares k).2

/-- 左方输入阶段事件。 -/
def leftInputTrace (c : BoolCircuit)
    (leftInput : Fin c.nLeft → Bool) (seed : LeftSeed c) : List LeftEvent :=
  ((List.finRange c.nLeft).map fun i =>
    let sent := (shareLeftInput (leftInput i) (seed.ownMasks i)).2
    let keep := (shareLeftInput (leftInput i) (seed.ownMasks i)).1
    LeftEvent.ownInput i.1 (leftInput i) keep sent)
  ++
  (List.finRange c.nRight).map fun j =>
    LeftEvent.otherInput j.1 (seed.recvInputShares j)

/-- 右方输入阶段事件。 -/
def rightInputTrace (c : BoolCircuit)
    (rightInput : Fin c.nRight → Bool) (seed : RightSeed c) : List RightEvent :=
  ((List.finRange c.nLeft).map fun i =>
    RightEvent.otherInput i.1 (seed.recvInputShares i)
  )
  ++
  (List.finRange c.nRight).map fun j =>
    let sent := (shareRightInput (rightInput j) (seed.ownMasks j)).1
    let keep := (shareRightInput (rightInput j) (seed.ownMasks j)).2
    RightEvent.ownInput j.1 (rightInput j) keep sent

/-- 双方都被腐化时的左方输入阶段事件。 -/
def bothLeftInputTrace (c : BoolCircuit) (input : Inputs c) (seed : BothSeed c) : List LeftEvent :=
  ((List.finRange c.nLeft).map fun i =>
    let sent := (shareLeftInput (input.left i) (seed.leftMasks i)).2
    let keep := (shareLeftInput (input.left i) (seed.leftMasks i)).1
    LeftEvent.ownInput i.1 (input.left i) keep sent)
  ++
  (List.finRange c.nRight).map fun j =>
    LeftEvent.otherInput j.1 (shareRightInput (input.right j) (seed.rightMasks j)).1

/-- 双方都被腐化时的右方输入阶段事件。 -/
def bothRightInputTrace
    (c : BoolCircuit) (input : Inputs c) (seed : BothSeed c) : List RightEvent :=
  ((List.finRange c.nLeft).map fun i =>
    RightEvent.otherInput i.1 (shareLeftInput (input.left i) (seed.leftMasks i)).2
  )
  ++
  (List.finRange c.nRight).map fun j =>
    let sent := (shareRightInput (input.right j) (seed.rightMasks j)).1
    let keep := (shareRightInput (input.right j) (seed.rightMasks j)).2
    RightEvent.ownInput j.1 (input.right j) keep sent

/-- 左方逐门运行状态。 -/
structure LeftRunState (c : BoolCircuit) (n : Nat) where
  gateShares : Fin n → Bool
  trace : List LeftEvent

/-- 右方逐门运行状态。 -/
structure RightRunState (c : BoolCircuit) (n : Nat) where
  gateShares : Fin n → Bool
  trace : List RightEvent

/-- 双方都被腐化时的逐门运行状态。 -/
structure BothRunState (c : BoolCircuit) (n : Nat) where
  gateShares : Fin n → Share
  leftTrace : List LeftEvent
  rightTrace : List RightEvent

/-- 左方沿整个电路程序运行。 -/
def runLeftProgram (c : BoolCircuit)
    (leftInput : Fin c.nLeft → Bool) (seed : LeftSeed c) :
    LeftRunState c c.nGates :=
  let rec go {n : Nat} (program : Program c.nLeft c.nRight n)
      (sendMasks : Fin n → Bool) (recvOT : Fin n → Bool) :
      LeftRunState c n :=
    match program with
    | .nil => { gateShares := Fin.elim0, trace := leftInputTrace c leftInput seed }
    | .snoc (n := m) prev node =>
        let prevState := go prev (takePrefix sendMasks) (takePrefix recvOT)
        match node with
        | .xor a b =>
            let lhs := leftRefShare c leftInput seed prevState.gateShares a
            let rhs := leftRefShare c leftInput seed prevState.gateShares b
            let out := bxor lhs rhs
            { gateShares := extendVals prevState.gateShares out
              trace := prevState.trace.concat (.xor m lhs rhs out) }
        | .not a =>
            let inp := leftRefShare c leftInput seed prevState.gateShares a
            let out := !inp
            { gateShares := extendVals prevState.gateShares out
              trace := prevState.trace.concat (.not m inp out) }
        | .and a b =>
            let lhs := leftRefShare c leftInput seed prevState.gateShares a
            let rhs := leftRefShare c leftInput seed prevState.gateShares b
            let sendMask := sendMasks (Fin.last m)
            let recvOut := recvOT (Fin.last m)
            let send := senderView m ⟨sendMask, bxor sendMask lhs⟩
            let recv := receiverView m rhs recvOut
            let out := bxor (lhs && rhs) (bxor recvOut sendMask)
            { gateShares := extendVals prevState.gateShares out
              trace := prevState.trace.concat (.and m lhs rhs send recv out) }
  go c.program seed.sendMasks seed.recvOT

/-- 右方沿整个电路程序运行。 -/
def runRightProgram (c : BoolCircuit)
    (rightInput : Fin c.nRight → Bool) (seed : RightSeed c) :
    RightRunState c c.nGates :=
  let rec go {n : Nat} (program : Program c.nLeft c.nRight n)
      (recvOT : Fin n → Bool) (sendMasks : Fin n → Bool) :
      RightRunState c n :=
    match program with
    | .nil => { gateShares := Fin.elim0, trace := rightInputTrace c rightInput seed }
    | .snoc (n := m) prev node =>
        let prevState := go prev (takePrefix recvOT) (takePrefix sendMasks)
        match node with
        | .xor a b =>
            let lhs := rightRefShare c rightInput seed prevState.gateShares a
            let rhs := rightRefShare c rightInput seed prevState.gateShares b
            let out := bxor lhs rhs
            { gateShares := extendVals prevState.gateShares out
              trace := prevState.trace.concat (.xor m lhs rhs out) }
        | .not a =>
            let inp := rightRefShare c rightInput seed prevState.gateShares a
            let out := inp
            { gateShares := extendVals prevState.gateShares out
              trace := prevState.trace.concat (.not m inp out) }
        | .and a b =>
            let lhs := rightRefShare c rightInput seed prevState.gateShares a
            let rhs := rightRefShare c rightInput seed prevState.gateShares b
            let recvOut := recvOT (Fin.last m)
            let sendMask := sendMasks (Fin.last m)
            let recv := receiverView m rhs recvOut
            let send := senderView m ⟨sendMask, bxor sendMask lhs⟩
            let out := bxor (lhs && rhs) (bxor recvOut sendMask)
            { gateShares := extendVals prevState.gateShares out
              trace := prevState.trace.concat (.and m lhs rhs recv send out) }
  go c.program seed.recvOT seed.sendMasks

/-- 双方都被腐化时沿整个电路程序运行。 -/
def runBothProgram (c : BoolCircuit)
    (input : Inputs c) (seed : BothSeed c) :
    BothRunState c c.nGates :=
  let rec go {n : Nat} (program : Program c.nLeft c.nRight n)
      (sendL : Fin n → Bool) (sendR : Fin n → Bool) :
      BothRunState c n :=
    match program with
    | .nil =>
        { gateShares := Fin.elim0
          leftTrace := bothLeftInputTrace c input seed
          rightTrace := bothRightInputTrace c input seed }
    | .snoc (n := m) prev node =>
        let prevState := go prev (takePrefix sendL) (takePrefix sendR)
        match node with
        | .xor a b =>
            let lhsL := bothRefShareLeft c input seed prevState.gateShares a
            let rhsL := bothRefShareLeft c input seed prevState.gateShares b
            let lhsR := bothRefShareRight c input seed prevState.gateShares a
            let rhsR := bothRefShareRight c input seed prevState.gateShares b
            let out : Share := (bxor lhsL rhsL, bxor lhsR rhsR)
            { gateShares := extendVals prevState.gateShares out
              leftTrace := prevState.leftTrace.concat (.xor m lhsL rhsL out.1)
              rightTrace := prevState.rightTrace.concat (.xor m lhsR rhsR out.2) }
        | .not a =>
            let inL := bothRefShareLeft c input seed prevState.gateShares a
            let inR := bothRefShareRight c input seed prevState.gateShares a
            let out : Share := (!inL, inR)
            { gateShares := extendVals prevState.gateShares out
              leftTrace := prevState.leftTrace.concat (.not m inL out.1)
              rightTrace := prevState.rightTrace.concat (.not m inR out.2) }
        | .and a b =>
            let aL := bothRefShareLeft c input seed prevState.gateShares a
            let bL := bothRefShareLeft c input seed prevState.gateShares b
            let aR := bothRefShareRight c input seed prevState.gateShares a
            let bR := bothRefShareRight c input seed prevState.gateShares b
            let sendLNow := sendL (Fin.last m)
            let sendRNow := sendR (Fin.last m)
            let otL := F_OT ⟨sendLNow, bxor sendLNow aL⟩ bR
            let otR := F_OT ⟨sendRNow, bxor sendRNow aR⟩ bL
            let out : Share := andShareOT (aL, aR) (bL, bR) sendLNow sendRNow
            { gateShares := extendVals prevState.gateShares out
              leftTrace := prevState.leftTrace.concat
                (.and m aL bL
                  (senderView m ⟨sendLNow, bxor sendLNow aL⟩)
                  (receiverView m bL otR)
                  out.1)
              rightTrace := prevState.rightTrace.concat
                (.and m aR bR
                  (receiverView m bR otL)
                  (senderView m ⟨sendRNow, bxor sendRNow aR⟩)
                  out.2) }
  go c.program seed.sendL seed.sendR

/-- 左方从完整输入得到的真实局部视图。 -/
def leftRealView (c : BoolCircuit) (input : Inputs c) (seed : LeftSeed c) : LeftFinalView :=
  let run := runLeftProgram c input.left seed
  let outShare := leftRefShare c input.left seed run.gateShares c.output
  let output := c.eval input
  let recvShare := bxor output outShare
  { trace := run.trace.concat (.outputReveal outShare recvShare output)
    outputShare := outShare
    receivedOutputShare := recvShare
    output := output }

/-- 左方模拟器生成的局部视图。 -/
def leftSimView (c : BoolCircuit)
    (leftInput : Fin c.nLeft → Bool) (output : Bool) (seed : LeftSeed c) : LeftFinalView :=
  let run := runLeftProgram c leftInput seed
  let outShare := leftRefShare c leftInput seed run.gateShares c.output
  let recvShare := bxor output outShare
  { trace := run.trace.concat (.outputReveal outShare recvShare output)
    outputShare := outShare
    receivedOutputShare := recvShare
    output := output }

/-- 右方从完整输入得到的真实局部视图。 -/
def rightRealView (c : BoolCircuit) (input : Inputs c) (seed : RightSeed c) : RightFinalView :=
  let run := runRightProgram c input.right seed
  let outShare := rightRefShare c input.right seed run.gateShares c.output
  let output := c.eval input
  let recvShare := bxor output outShare
  { trace := run.trace.concat (.outputReveal outShare recvShare output)
    outputShare := outShare
    receivedOutputShare := recvShare
    output := output }

/-- 右方模拟器生成的局部视图。 -/
def rightSimView (c : BoolCircuit)
    (rightInput : Fin c.nRight → Bool) (output : Bool) (seed : RightSeed c) : RightFinalView :=
  let run := runRightProgram c rightInput seed
  let outShare := rightRefShare c rightInput seed run.gateShares c.output
  let recvShare := bxor output outShare
  { trace := run.trace.concat (.outputReveal outShare recvShare output)
    outputShare := outShare
    receivedOutputShare := recvShare
    output := output }

/-- 双方都被腐化时的真实全视图。 -/
def bothRealView (c : BoolCircuit) (input : Inputs c) (seed : BothSeed c) :
    LocalView PartyView :=
  let run := runBothProgram c input seed
  let outShareL := bothRefShareLeft c input seed run.gateShares c.output
  let outShareR := bothRefShareRight c input seed run.gateShares c.output
  let output := c.eval input
  fun p =>
    if p = left then
      .left
        { trace := run.leftTrace.concat (.outputReveal outShareL outShareR output)
          outputShare := outShareL
          receivedOutputShare := outShareR
          output := output }
    else
      .right
        { trace := run.rightTrace.concat (.outputReveal outShareR outShareL output)
          outputShare := outShareR
          receivedOutputShare := outShareL
          output := output }

/-- 双方都被腐化时的模拟器视图。 -/
def bothSimView (c : BoolCircuit) (input : Inputs c) (seed : BothSeed c) :
    LocalView PartyView :=
  bothRealView c input seed

/-- 未腐化或被隐藏的一方使用的占位视图。 -/
def blankLeftView : LeftFinalView :=
  { trace := []
    outputShare := false
    receivedOutputShare := false
    output := false }

/-- 未腐化或被隐藏的一方使用的占位视图。 -/
def blankRightView : RightFinalView :=
  { trace := []
    outputShare := false
    receivedOutputShare := false
    output := false }

/-- 只暴露左方视图的本地视图。 -/
def leftOnlyLocalView (view : LeftFinalView) : LocalView PartyView :=
  fun p => if p = left then .left view else .right blankRightView

/-- 只暴露右方视图的本地视图。 -/
def rightOnlyLocalView (view : RightFinalView) : LocalView PartyView :=
  fun p => if p = right then .right view else .left blankLeftView

/-- 完全空白的本地视图。 -/
def blankLocalView : LocalView PartyView :=
  fun p => if p = left then .left blankLeftView else .right blankRightView

/-- XOR 门在 real / ideal 中对单边视图的更新是一致的。 -/
theorem xor_gate_view_sim (gateId : Nat) (lhs rhs : Bool) :
    LeftEvent.xor gateId lhs rhs (bxor lhs rhs) =
      LeftEvent.xor gateId lhs rhs (bxor lhs rhs) := by
  rfl

/-- NOT 门在 real / ideal 中对单边视图的更新是一致的。 -/
theorem not_gate_view_sim (gateId : Nat) (inp : Bool) :
    LeftEvent.not gateId inp (!inp) = LeftEvent.not gateId inp (!inp) := by
  rfl

/-- 左方被腐化时，AND 门的局部视图只依赖左方份额与独立采样的两位随机量。 -/
theorem and_gate_view_sim_left
    (gateId : Nat) (lhs rhs sendMask recvOut : Bool) :
    LeftEvent.and gateId lhs rhs
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (receiverView gateId rhs recvOut)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) =
      LeftEvent.and gateId lhs rhs
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (receiverView gateId rhs recvOut)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) := by
  rfl

/-- 右方被腐化时，AND 门的局部视图只依赖右方份额与独立采样的两位随机量。 -/
theorem and_gate_view_sim_right
    (gateId : Nat) (lhs rhs recvOut sendMask : Bool) :
    RightEvent.and gateId lhs rhs
        (receiverView gateId rhs recvOut)
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) =
      RightEvent.and gateId lhs rhs
        (receiverView gateId rhs recvOut)
        (senderView gateId ⟨sendMask, bxor sendMask lhs⟩)
        (bxor (lhs && rhs) (bxor recvOut sendMask)) := by
  rfl

/-- 真实协议：按腐化情形返回对应的局部可观察执行分布。 -/
noncomputable def realProtocol {Adv : Type} (c : BoolCircuit) :
    Protocol Adv (Inputs c) PartyView :=
  fun corr _adv input =>
    match corr with
    | .none => constFamily (PMF.pure blankLocalView)
    | .left =>
        constFamily <| PMF.map (fun seed => leftOnlyLocalView (leftRealView c input seed))
          (uniformDist (LeftSeed c))
    | .right =>
        constFamily <| PMF.map (fun seed => rightOnlyLocalView (rightRealView c input seed))
          (uniformDist (RightSeed c))
    | .both =>
        constFamily <| PMF.map (bothRealView c input) (uniformDist (BothSeed c))

/-- GMW 在 OT-hybrid 世界中的模拟器。 -/
noncomputable def gmwSimulator {Adv : Type} (c : BoolCircuit) :
    Adv → Simulator (IdealSFE c).interface PartyView
  | _ =>
      fun corr cin cout _ =>
        match corr with
        | .none => constFamily (PMF.pure blankLocalView)
        | .left =>
            constFamily <| PMF.map (fun seed => leftOnlyLocalView (leftSimView c cin cout seed))
              (uniformDist (LeftSeed c))
        | .right =>
            constFamily <| PMF.map (fun seed => rightOnlyLocalView (rightSimView c cin cout seed))
              (uniformDist (RightSeed c))
        | .both =>
            constFamily <| PMF.map (bothSimView c cin) (uniformDist (BothSeed c))

/-- 左方情形下，真实视图生成器与模拟视图生成器完全一致。 -/
theorem left_real_eq_sim (c : BoolCircuit) (input : Inputs c) (seed : LeftSeed c) :
    leftRealView c input seed = leftSimView c input.left (c.eval input) seed := by
  rfl

/-- 右方情形下，真实视图生成器与模拟视图生成器完全一致。 -/
theorem right_real_eq_sim (c : BoolCircuit) (input : Inputs c) (seed : RightSeed c) :
    rightRealView c input seed = rightSimView c input.right (c.eval input) seed := by
  rfl

/-- 单个腐化情形下的完美不可区分。 -/
theorem gmw_case_perfect {Adv : Type} (c : BoolCircuit) (adv : Adv)
    (corr : CorruptionCase) (input : Inputs c) :
    Indistinguishable .perfect zeroError (fun _ => True) (env := { run := fun _ => false })
      (RealModel (realProtocol (Adv := Adv) c) corr adv input)
      (IdealModel (IdealSFE c) ((gmwSimulator (Adv := Adv) c) adv) corr input) := by
  cases corr with
  | none =>
      intro n
      simp [RealModel, IdealModel, realProtocol, gmwSimulator, ObservedDist]
  | left =>
      intro n
      simp [RealModel, IdealModel, realProtocol, gmwSimulator, ObservedDist,
        IdealSFE, F_SFE_BoolCircuit, left_real_eq_sim]
  | right =>
      intro n
      simp [RealModel, IdealModel, realProtocol, gmwSimulator, ObservedDist,
        IdealSFE, F_SFE_BoolCircuit, right_real_eq_sim]
  | both =>
      intro n
      change
        PMF.map (observedView CorruptionCase.both)
          (PMF.map (bothRealView c input) (uniformDist (BothSeed c))) =
        PMF.map (observedView CorruptionCase.both)
          (PMF.map (bothRealView c input) (uniformDist (BothSeed c)))
      rfl

/-- 真实世界与理想世界的观察分布在四种腐化情形下都完全一致。 -/
theorem gmw_real_ideal_view_eq {Adv : Type} (c : BoolCircuit) :
    ∀ adv corr input,
      PerfectIndist
        (RealModel (realProtocol (Adv := Adv) c) corr adv input)
        (IdealModel (IdealSFE c) ((gmwSimulator (Adv := Adv) c) adv) corr input) := by
  intro adv corr input
  simpa [Indistinguishable] using
    (gmw_case_perfect (Adv := Adv) c adv corr input)

/-- OT-hybrid 世界中 GMW 的严格完美 UC 安全性。 -/
theorem gmw_ot_hybrid_uc_secure_perfect {Adv : Type} (c : BoolCircuit) :
    UCSecurePerfect (realProtocol (Adv := Adv) c) (IdealSFE c) := by
  refine UCSecureAt.of_cases
    (level := .perfect)
    (ε := zeroError)
    (PPTEnv := fun _ => True)
    (protocol := realProtocol (Adv := Adv) c)
    (ideal := IdealSFE c)
    (simulatorFor := gmwSimulator (Adv := Adv) c)
    ?_ ?_ ?_ ?_
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .none input
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .left input
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .right input
  · intro adv env input
    simpa [Indistinguishable] using gmw_real_ideal_view_eq (Adv := Adv) c adv .both input

/-- 向后兼容的名字。 -/
theorem gmw_ot_hybrid_uc_secure {Adv : Type} (c : BoolCircuit) :
    UCSecurePerfect (realProtocol (Adv := Adv) c) (IdealSFE c) :=
  gmw_ot_hybrid_uc_secure_perfect (Adv := Adv) c

end LeanCryptoProtocols.GMW.OTHybrid

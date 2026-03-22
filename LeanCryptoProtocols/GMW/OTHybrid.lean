import LeanCryptoProtocols.UC.Core
import LeanCryptoProtocols.UC.Functionality.OT

/-!
# OT-hybrid 世界中的 GMW

本文件实现一个面向第一阶段的 GMW 形式化：

- 两方；
- 半诚实、静态腐化；
- 布尔电路；
- `F_OT`-hybrid 世界；
- 用被腐化方可观察视图的 support 相等来表达完美安全。

为了让证明保持可控，当前电路 IR 采用树形布尔电路。
这已经足以承载 XOR 免费、AND 走 `F_OT` 的 GMW 证明骨架。
-/

namespace LeanCryptoProtocols.GMW.OTHybrid

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Functionality

/-- `Bool.xor` 的简写。 -/
abbrev bxor : Bool → Bool → Bool := Bool.xor

mutual

/-- 电路中的 wire。 -/
inductive Wire : Nat → Nat → Type
  | inputL {nLeft nRight : Nat} : Fin nLeft → Wire nLeft nRight
  | inputR {nLeft nRight : Nat} : Fin nRight → Wire nLeft nRight
  | gate {nLeft nRight : Nat} : Gate nLeft nRight → Wire nLeft nRight
  deriving DecidableEq, Repr

/-- 第一版只保留 XOR 与 AND 两类内部 gate。 -/
inductive Gate : Nat → Nat → Type
  | xor {nLeft nRight : Nat} : Nat → Wire nLeft nRight → Wire nLeft nRight → Gate nLeft nRight
  | and {nLeft nRight : Nat} : Nat → Wire nLeft nRight → Wire nLeft nRight → Gate nLeft nRight
  deriving DecidableEq, Repr

end

/-- 单输出布尔电路。 -/
structure BoolCircuit where
  nLeft : Nat
  nRight : Nat
  output : Wire nLeft nRight

/-- GMW 的输入。 -/
structure Inputs (c : BoolCircuit) where
  left : Fin c.nLeft → Bool
  right : Fin c.nRight → Bool

mutual

/-- 递归求值 wire。 -/
def evalWire {nLeft nRight : Nat} :
    Wire nLeft nRight → (Fin nLeft → Bool) → (Fin nRight → Bool) → Bool
  | .inputL i, x, _ => x i
  | .inputR j, _, y => y j
  | .gate g, x, y => evalGate g x y

/-- 递归求值 gate。 -/
def evalGate {nLeft nRight : Nat} :
    Gate nLeft nRight → (Fin nLeft → Bool) → (Fin nRight → Bool) → Bool
  | .xor _ a b, x, y => bxor (evalWire a x y) (evalWire b x y)
  | .and _ a b, x, y => evalWire a x y && evalWire b x y

end

/-- 电路理想功能的输出。 -/
def F_SFE_BoolCircuit (c : BoolCircuit) (input : Inputs c) : Bool :=
  evalWire c.output input.left input.right

/-- 两方 bit 共享。 -/
abbrev Share : Type := Bool × Bool

/-- 还原共享值。 -/
def revealShare (s : Share) : Bool :=
  bxor s.1 s.2

/-- 左方输入的 GMW 分享。 -/
def shareLeftInput (x mask : Bool) : Share :=
  (mask, bxor x mask)

/-- 右方输入的 GMW 分享。 -/
def shareRightInput (x mask : Bool) : Share :=
  (mask, bxor x mask)

/-- XOR 门逐份额按位异或。 -/
def xorShare (a b : Share) : Share :=
  (bxor a.1 b.1, bxor a.2 b.2)

/-- AND 门中两次 OT 用到的随机量。 -/
structure AndRandomness where
  fromLeft : Bool
  fromRight : Bool
  deriving Repr, DecidableEq

/-- 左向右 OT 的接收输出。 -/
def leftToRightOTOutput (aLeft bRight mask : Bool) : Bool :=
  bxor mask (aLeft && bRight)

/-- 右向左 OT 的接收输出。 -/
def rightToLeftOTOutput (aRight bLeft mask : Bool) : Bool :=
  bxor mask (aRight && bLeft)

/--
OT-hybrid AND 子协议产生的输出共享。

这是标准两次 OT 写法：
- 左方发送 `(r, r xor a0)`；
- 右方发送 `(s, s xor a1)`；
- 各自用收到的 OT 输出完成交叉项。
-/
def andShareOT (a b : Share) (ρ : AndRandomness) : Share :=
  let t := leftToRightOTOutput a.1 b.2 ρ.fromLeft
  let u := rightToLeftOTOutput a.2 b.1 ρ.fromRight
  (bxor (a.1 && b.1) (bxor u ρ.fromLeft),
    bxor (a.2 && b.2) (bxor t ρ.fromRight))

/-- XOR 门共享正确性。 -/
theorem gmw_xor_gate_correct (a b : Share) :
    revealShare (xorShare a b) = bxor (revealShare a) (revealShare b) := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

/-- AND 门 OT-hybrid 子协议正确性。 -/
theorem gmw_and_gate_ot_hybrid_correct (a b : Share) (ρ : AndRandomness) :
    revealShare (andShareOT a b ρ) = (revealShare a && revealShare b) := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  rcases ρ with ⟨r, s⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases r <;> cases s <;> rfl

@[simp] theorem rightToLeftOTOutput_cancel (aRight bLeft recvOut : Bool) :
    rightToLeftOTOutput aRight bLeft (bxor recvOut (aRight && bLeft)) = recvOut := by
  cases aRight <;> cases bLeft <;> cases recvOut <;> rfl

@[simp] theorem leftToRightOTOutput_cancel (aLeft bRight recvOut : Bool) :
    leftToRightOTOutput aLeft bRight (bxor recvOut (aLeft && bRight)) = recvOut := by
  cases aLeft <;> cases bRight <;> cases recvOut <;> rfl

/-- 真实执行使用的随机种子。 -/
inductive RealSeed : {nLeft nRight : Nat} → Wire nLeft nRight → Type
  | inputL {nLeft nRight : Nat} (i : Fin nLeft) (mask : Bool) :
      RealSeed (Wire.inputL (nLeft := nLeft) (nRight := nRight) i)
  | inputR {nLeft nRight : Nat} (i : Fin nRight) (mask : Bool) :
      RealSeed (Wire.inputR (nLeft := nLeft) (nRight := nRight) i)
  | xor {nLeft nRight : Nat} (id : Nat) {a b : Wire nLeft nRight}
      (sa : RealSeed a) (sb : RealSeed b) :
      RealSeed (Wire.gate (Gate.xor id a b))
  | and {nLeft nRight : Nat} (id : Nat) {a b : Wire nLeft nRight}
      (sa : RealSeed a) (sb : RealSeed b) (ρ : AndRandomness) :
      RealSeed (Wire.gate (Gate.and id a b))

/-- 左方模拟器使用的可观察种子。 -/
inductive LeftObsSeed : {nLeft nRight : Nat} → Wire nLeft nRight → Type
  | inputOwn {nLeft nRight : Nat} (i : Fin nLeft) (mask : Bool) :
      LeftObsSeed (Wire.inputL (nLeft := nLeft) (nRight := nRight) i)
  | inputOther {nLeft nRight : Nat} (i : Fin nRight) (share : Bool) :
      LeftObsSeed (Wire.inputR (nLeft := nLeft) (nRight := nRight) i)
  | xor {nLeft nRight : Nat} (id : Nat) {a b : Wire nLeft nRight}
      (sa : LeftObsSeed a) (sb : LeftObsSeed b) :
      LeftObsSeed (Wire.gate (Gate.xor id a b))
  | and {nLeft nRight : Nat} (id : Nat) {a b : Wire nLeft nRight}
      (sa : LeftObsSeed a) (sb : LeftObsSeed b)
      (sendMask recvOut : Bool) :
      LeftObsSeed (Wire.gate (Gate.and id a b))

/-- 右方模拟器使用的可观察种子。 -/
inductive RightObsSeed : {nLeft nRight : Nat} → Wire nLeft nRight → Type
  | inputOther {nLeft nRight : Nat} (i : Fin nLeft) (share : Bool) :
      RightObsSeed (Wire.inputL (nLeft := nLeft) (nRight := nRight) i)
  | inputOwn {nLeft nRight : Nat} (i : Fin nRight) (mask : Bool) :
      RightObsSeed (Wire.inputR (nLeft := nLeft) (nRight := nRight) i)
  | xor {nLeft nRight : Nat} (id : Nat) {a b : Wire nLeft nRight}
      (sa : RightObsSeed a) (sb : RightObsSeed b) :
      RightObsSeed (Wire.gate (Gate.xor id a b))
  | and {nLeft nRight : Nat} (id : Nat) {a b : Wire nLeft nRight}
      (sa : RightObsSeed a) (sb : RightObsSeed b)
      (sendMask recvOut : Bool) :
      RightObsSeed (Wire.gate (Gate.and id a b))

mutual

/-- 由真实种子与双方输入计算两方共享。 -/
def realShareOf {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : Share :=
  match seed with
  | .inputL i mask => shareLeftInput (x i) mask
  | .inputR i mask => shareRightInput (y i) mask
  | .xor _ sa sb => xorShare (realShareOf sa x y) (realShareOf sb x y)
  | .and _ sa sb ρ => andShareOT (realShareOf sa x y) (realShareOf sb x y) ρ

/-- 左方在可观察种子下持有的局部份额。 -/
def leftShareOf {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : LeftObsSeed w) (x : Fin nLeft → Bool) : Bool :=
  match seed with
  | .inputOwn i mask => (shareLeftInput (x i) mask).1
  | .inputOther _ share => share
  | .xor _ sa sb => bxor (leftShareOf sa x) (leftShareOf sb x)
  | .and _ sa sb sendMask recvOut =>
      bxor ((leftShareOf sa x) && (leftShareOf sb x)) (bxor recvOut sendMask)

/-- 右方在可观察种子下持有的局部份额。 -/
def rightShareOf {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RightObsSeed w) (y : Fin nRight → Bool) : Bool :=
  match seed with
  | .inputOther _ share => share
  | .inputOwn i mask => (shareRightInput (y i) mask).2
  | .xor _ sa sb => bxor (rightShareOf sa y) (rightShareOf sb y)
  | .and _ sa sb sendMask recvOut =>
      bxor ((rightShareOf sa y) && (rightShareOf sb y)) (bxor recvOut sendMask)

end

/-- 左方的逐门可观察 trace。 -/
inductive LeftTrace where
  | inputOwn : Nat → Bool → Bool → LeftTrace
  | inputOther : Nat → Bool → LeftTrace
  | xor : Nat → LeftTrace → LeftTrace → Bool → LeftTrace
  | and : Nat → LeftTrace → LeftTrace →
      Bool → Bool → Bool → Bool → Bool → LeftTrace
  deriving Repr, DecidableEq

/-- 右方的逐门可观察 trace。 -/
inductive RightTrace where
  | inputOther : Nat → Bool → RightTrace
  | inputOwn : Nat → Bool → Bool → RightTrace
  | xor : Nat → RightTrace → RightTrace → Bool → RightTrace
  | and : Nat → RightTrace → RightTrace →
      Bool → Bool → Bool → Bool → Bool → RightTrace
  deriving Repr, DecidableEq

mutual

/-- 真实执行中左方的局部 trace。 -/
def leftRealTrace {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : LeftTrace :=
  match seed with
  | .inputL i mask =>
      LeftTrace.inputOwn i.1 (x i) (shareLeftInput (x i) mask).1
  | .inputR i mask =>
      LeftTrace.inputOther i.1 (shareRightInput (y i) mask).1
  | .xor id sa sb =>
      LeftTrace.xor id (leftRealTrace sa x y) (leftRealTrace sb x y) (realShareOf seed x y).1
  | .and id sa sb ρ =>
      let a := realShareOf sa x y
      let b := realShareOf sb x y
      LeftTrace.and id
        (leftRealTrace sa x y)
        (leftRealTrace sb x y)
        (realShareOf seed x y).1
        ρ.fromLeft
        (bxor ρ.fromLeft a.1)
        b.1
        (rightToLeftOTOutput a.2 b.1 ρ.fromRight)

/-- 真实执行中右方的局部 trace。 -/
def rightRealTrace {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : RightTrace :=
  match seed with
  | .inputL i mask =>
      RightTrace.inputOther i.1 (shareLeftInput (x i) mask).2
  | .inputR i mask =>
      RightTrace.inputOwn i.1 (y i) (shareRightInput (y i) mask).2
  | .xor id sa sb =>
      RightTrace.xor id (rightRealTrace sa x y) (rightRealTrace sb x y) (realShareOf seed x y).2
  | .and id sa sb ρ =>
      let a := realShareOf sa x y
      let b := realShareOf sb x y
      RightTrace.and id
        (rightRealTrace sa x y)
        (rightRealTrace sb x y)
        (realShareOf seed x y).2
        ρ.fromRight
        (bxor ρ.fromRight a.2)
        b.2
        (leftToRightOTOutput a.1 b.2 ρ.fromLeft)

/-- 理想世界中左方的模拟 trace。 -/
def leftSimTrace {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : LeftObsSeed w) (x : Fin nLeft → Bool) : LeftTrace :=
  match seed with
  | .inputOwn i mask =>
      LeftTrace.inputOwn i.1 (x i) (shareLeftInput (x i) mask).1
  | .inputOther i share =>
      LeftTrace.inputOther i.1 share
  | .xor id sa sb =>
      LeftTrace.xor id (leftSimTrace sa x) (leftSimTrace sb x) (leftShareOf seed x)
  | .and id sa sb sendMask recvOut =>
      LeftTrace.and id
        (leftSimTrace sa x)
        (leftSimTrace sb x)
        (leftShareOf seed x)
        sendMask
        (bxor sendMask (leftShareOf sa x))
        (leftShareOf sb x)
        recvOut

/-- 理想世界中右方的模拟 trace。 -/
def rightSimTrace {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RightObsSeed w) (y : Fin nRight → Bool) : RightTrace :=
  match seed with
  | .inputOther i share =>
      RightTrace.inputOther i.1 share
  | .inputOwn i mask =>
      RightTrace.inputOwn i.1 (y i) (shareRightInput (y i) mask).2
  | .xor id sa sb =>
      RightTrace.xor id (rightSimTrace sa y) (rightSimTrace sb y) (rightShareOf seed y)
  | .and id sa sb sendMask recvOut =>
      RightTrace.and id
        (rightSimTrace sa y)
        (rightSimTrace sb y)
        (rightShareOf seed y)
        sendMask
        (bxor sendMask (rightShareOf sa y))
        (rightShareOf sb y)
        recvOut

end

/-- 左方最终视图：逐门 trace 加上最终输出。 -/
structure LeftFinalView where
  trace : LeftTrace
  output : Bool
  deriving Repr, DecidableEq

/-- 右方最终视图：逐门 trace 加上最终输出。 -/
structure RightFinalView where
  trace : RightTrace
  output : Bool
  deriving Repr, DecidableEq

/-- 两方本地视图统一到一个总类型中。 -/
inductive PartyView where
  | left : LeftFinalView → PartyView
  | right : RightFinalView → PartyView
  deriving Repr, DecidableEq

mutual

/-- 从真实种子中抽取左方可观察种子。 -/
def projectLeftSeed {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : LeftObsSeed w :=
  match seed with
  | .inputL i mask => .inputOwn i mask
  | .inputR i mask => .inputOther i (shareRightInput (y i) mask).1
  | .xor id sa sb => .xor id (projectLeftSeed sa x y) (projectLeftSeed sb x y)
  | .and id sa sb ρ =>
      let a := realShareOf sa x y
      let b := realShareOf sb x y
      .and id (projectLeftSeed sa x y) (projectLeftSeed sb x y)
        ρ.fromLeft
        (rightToLeftOTOutput a.2 b.1 ρ.fromRight)

/-- 从真实种子中抽取右方可观察种子。 -/
def projectRightSeed {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : RightObsSeed w :=
  match seed with
  | .inputL i mask => .inputOther i (shareLeftInput (x i) mask).2
  | .inputR i mask => .inputOwn i mask
  | .xor id sa sb => .xor id (projectRightSeed sa x y) (projectRightSeed sb x y)
  | .and id sa sb ρ =>
      let a := realShareOf sa x y
      let b := realShareOf sb x y
      .and id (projectRightSeed sa x y) (projectRightSeed sb x y)
        ρ.fromRight
        (leftToRightOTOutput a.1 b.2 ρ.fromLeft)

/-- 用左方可观察种子回填出一个真实种子。 -/
def liftLeftSeed {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : LeftObsSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : RealSeed w :=
  match seed with
  | .inputOwn i mask => .inputL i mask
  | .inputOther i share => .inputR i share
  | .xor id sa sb => .xor id (liftLeftSeed sa x y) (liftLeftSeed sb x y)
  | .and id sa sb sendMask recvOut =>
      let ra := liftLeftSeed sa x y
      let rb := liftLeftSeed sb x y
      let a := realShareOf ra x y
      let b := realShareOf rb x y
      .and id ra rb ⟨sendMask, bxor recvOut (a.2 && b.1)⟩

/-- 用右方可观察种子回填出一个真实种子。 -/
def liftRightSeed {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RightObsSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) : RealSeed w :=
  match seed with
  | .inputOther i share => .inputL i (bxor (x i) share)
  | .inputOwn i mask => .inputR i mask
  | .xor id sa sb => .xor id (liftRightSeed sa x y) (liftRightSeed sb x y)
  | .and id sa sb sendMask recvOut =>
      let ra := liftRightSeed sa x y
      let rb := liftRightSeed sb x y
      let a := realShareOf ra x y
      let b := realShareOf rb x y
      .and id ra rb ⟨bxor recvOut (a.1 && b.2), sendMask⟩

end

theorem leftShare_project_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    leftShareOf (projectLeftSeed seed x y) x = (realShareOf seed x y).1 := by
  induction seed with
  | inputL i mask =>
      simp [projectLeftSeed, leftShareOf, realShareOf, shareLeftInput]
  | inputR i mask =>
      simp [projectLeftSeed, leftShareOf, realShareOf, shareRightInput]
  | xor id sa sb iha ihb =>
      simp [projectLeftSeed, leftShareOf, realShareOf, iha, ihb, xorShare]
  | and id sa sb ρ iha ihb =>
      simp [projectLeftSeed, leftShareOf, realShareOf, iha, ihb, andShareOT,
        rightToLeftOTOutput]

theorem rightShare_project_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    rightShareOf (projectRightSeed seed x y) y = (realShareOf seed x y).2 := by
  induction seed with
  | inputL i mask =>
      simp [projectRightSeed, rightShareOf, realShareOf, shareLeftInput]
  | inputR i mask =>
      simp [projectRightSeed, rightShareOf, realShareOf, shareRightInput]
  | xor id sa sb iha ihb =>
      simp [projectRightSeed, rightShareOf, realShareOf, iha, ihb, xorShare]
  | and id sa sb ρ iha ihb =>
      simp [projectRightSeed, rightShareOf, realShareOf, iha, ihb, andShareOT,
        leftToRightOTOutput]

theorem leftShare_lift_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : LeftObsSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    leftShareOf seed x = (realShareOf (liftLeftSeed seed x y) x y).1 := by
  induction seed with
  | inputOwn i mask =>
      simp [liftLeftSeed, leftShareOf, realShareOf, shareLeftInput]
  | inputOther i share =>
      simp [liftLeftSeed, leftShareOf, realShareOf, shareRightInput]
  | xor id sa sb iha ihb =>
      simp [liftLeftSeed, leftShareOf, realShareOf, iha, ihb, xorShare]
  | and id sa sb sendMask recvOut iha ihb =>
      simp [liftLeftSeed, leftShareOf, realShareOf, iha, ihb, andShareOT]

theorem rightShare_lift_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RightObsSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    rightShareOf seed y = (realShareOf (liftRightSeed seed x y) x y).2 := by
  induction seed with
  | inputOther i share =>
      simp [liftRightSeed, rightShareOf, realShareOf, shareLeftInput]
  | inputOwn i mask =>
      simp [liftRightSeed, rightShareOf, realShareOf, shareRightInput]
  | xor id sa sb iha ihb =>
      simp [liftRightSeed, rightShareOf, realShareOf, iha, ihb, xorShare]
  | and id sa sb sendMask recvOut iha ihb =>
      simp [liftRightSeed, rightShareOf, realShareOf, iha, ihb, andShareOT]

theorem leftTrace_project_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    leftRealTrace seed x y = leftSimTrace (projectLeftSeed seed x y) x := by
  induction seed with
  | inputL i mask =>
      simp [leftRealTrace, leftSimTrace, projectLeftSeed, shareLeftInput]
  | inputR i mask =>
      simp [leftRealTrace, leftSimTrace, projectLeftSeed, shareRightInput]
  | xor id sa sb iha ihb =>
      simpa [leftRealTrace, leftSimTrace, projectLeftSeed, iha, ihb] using
        congrArg
          (fun s =>
            LeftTrace.xor id
              (leftSimTrace (projectLeftSeed sa x y) x)
              (leftSimTrace (projectLeftSeed sb x y) x)
              s)
          ((leftShare_project_eq (seed := RealSeed.xor id sa sb) x y).symm)
  | and id sa sb ρ iha ihb =>
      have ha : leftShareOf (projectLeftSeed sa x y) x = (realShareOf sa x y).1 :=
        leftShare_project_eq sa x y
      have hb : leftShareOf (projectLeftSeed sb x y) x = (realShareOf sb x y).1 :=
        leftShare_project_eq sb x y
      have hshare :
          (realShareOf (RealSeed.and id sa sb ρ) x y).1 =
            leftShareOf
              (LeftObsSeed.and id (projectLeftSeed sa x y) (projectLeftSeed sb x y)
                ρ.fromLeft (bxor ρ.fromRight ((realShareOf sa x y).2 && (realShareOf sb x y).1)))
              x := by
        simp [realShareOf, leftShareOf, andShareOT, rightToLeftOTOutput, ha, hb]
      simpa [leftRealTrace, leftSimTrace, projectLeftSeed, iha, ihb, ha, hb,
        rightToLeftOTOutput] using
        congrArg
          (fun s =>
            LeftTrace.and id
              (leftRealTrace sa x y)
              (leftRealTrace sb x y)
              s
              ρ.fromLeft
              (bxor ρ.fromLeft (realShareOf sa x y).1)
              (realShareOf sb x y).1
              (bxor ρ.fromRight ((realShareOf sa x y).2 && (realShareOf sb x y).1)))
          hshare

theorem rightTrace_project_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RealSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    rightRealTrace seed x y = rightSimTrace (projectRightSeed seed x y) y := by
  induction seed with
  | inputL i mask =>
      simp [rightRealTrace, rightSimTrace, projectRightSeed, shareLeftInput]
  | inputR i mask =>
      simp [rightRealTrace, rightSimTrace, projectRightSeed, shareRightInput]
  | xor id sa sb iha ihb =>
      simpa [rightRealTrace, rightSimTrace, projectRightSeed, iha, ihb] using
        congrArg
          (fun s =>
            RightTrace.xor id
              (rightSimTrace (projectRightSeed sa x y) y)
              (rightSimTrace (projectRightSeed sb x y) y)
              s)
          ((rightShare_project_eq (seed := RealSeed.xor id sa sb) x y).symm)
  | and id sa sb ρ iha ihb =>
      have ha : rightShareOf (projectRightSeed sa x y) y = (realShareOf sa x y).2 :=
        rightShare_project_eq sa x y
      have hb : rightShareOf (projectRightSeed sb x y) y = (realShareOf sb x y).2 :=
        rightShare_project_eq sb x y
      have hshare :
          (realShareOf (RealSeed.and id sa sb ρ) x y).2 =
            rightShareOf
              (RightObsSeed.and id (projectRightSeed sa x y) (projectRightSeed sb x y)
                ρ.fromRight (bxor ρ.fromLeft ((realShareOf sa x y).1 && (realShareOf sb x y).2)))
              y := by
        simp [realShareOf, rightShareOf, andShareOT, leftToRightOTOutput, ha, hb]
      simpa [rightRealTrace, rightSimTrace, projectRightSeed, iha, ihb, ha, hb,
        leftToRightOTOutput] using
        congrArg
          (fun s =>
            RightTrace.and id
              (rightRealTrace sa x y)
              (rightRealTrace sb x y)
              s
              ρ.fromRight
              (bxor ρ.fromRight (realShareOf sa x y).2)
              (realShareOf sb x y).2
              (bxor ρ.fromLeft ((realShareOf sa x y).1 && (realShareOf sb x y).2)))
          hshare

theorem leftTrace_lift_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : LeftObsSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    leftSimTrace seed x = leftRealTrace (liftLeftSeed seed x y) x y := by
  induction seed with
  | inputOwn i mask =>
      simp [leftRealTrace, leftSimTrace, liftLeftSeed, shareLeftInput]
  | inputOther i share =>
      simp [leftRealTrace, leftSimTrace, liftLeftSeed, shareRightInput]
  | xor id sa sb iha ihb =>
      simpa [leftRealTrace, leftSimTrace, liftLeftSeed, iha, ihb] using
        congrArg
          (fun s =>
            LeftTrace.xor id
              (leftRealTrace (liftLeftSeed sa x y) x y)
              (leftRealTrace (liftLeftSeed sb x y) x y)
              s)
          (leftShare_lift_eq (seed := LeftObsSeed.xor id sa sb) x y)
  | and id sa sb sendMask recvOut iha ihb =>
      have ha : leftShareOf sa x = (realShareOf (liftLeftSeed sa x y) x y).1 :=
        leftShare_lift_eq sa x y
      have hb : leftShareOf sb x = (realShareOf (liftLeftSeed sb x y) x y).1 :=
        leftShare_lift_eq sb x y
      have hshare :
          leftShareOf (LeftObsSeed.and id sa sb sendMask recvOut) x =
            (realShareOf
                (RealSeed.and id (liftLeftSeed sa x y) (liftLeftSeed sb x y)
                  { fromLeft := sendMask
                    fromRight :=
                      bxor recvOut
                        ((realShareOf (liftLeftSeed sa x y) x y).2 &&
                          (realShareOf (liftLeftSeed sb x y) x y).1) })
                x y).1 := by
        simp [leftShareOf, realShareOf, andShareOT, ha, hb,
          rightToLeftOTOutput_cancel]
      simpa [leftRealTrace, leftSimTrace, liftLeftSeed, iha, ihb, ha, hb,
        rightToLeftOTOutput_cancel] using
        congrArg
          (fun s =>
            LeftTrace.and id
              (leftRealTrace (liftLeftSeed sa x y) x y)
              (leftRealTrace (liftLeftSeed sb x y) x y)
              s
              sendMask
              (bxor sendMask (realShareOf (liftLeftSeed sa x y) x y).1)
              (realShareOf (liftLeftSeed sb x y) x y).1
              recvOut)
          hshare

theorem rightTrace_lift_eq {nLeft nRight : Nat} {w : Wire nLeft nRight}
    (seed : RightObsSeed w) (x : Fin nLeft → Bool) (y : Fin nRight → Bool) :
    rightSimTrace seed y = rightRealTrace (liftRightSeed seed x y) x y := by
  induction seed with
  | inputOther i share =>
      simp [rightRealTrace, rightSimTrace, liftRightSeed, shareLeftInput]
  | inputOwn i mask =>
      simp [rightRealTrace, rightSimTrace, liftRightSeed, shareRightInput]
  | xor id sa sb iha ihb =>
      simpa [rightRealTrace, rightSimTrace, liftRightSeed, iha, ihb] using
        congrArg
          (fun s =>
            RightTrace.xor id
              (rightRealTrace (liftRightSeed sa x y) x y)
              (rightRealTrace (liftRightSeed sb x y) x y)
              s)
          (rightShare_lift_eq (seed := RightObsSeed.xor id sa sb) x y)
  | and id sa sb sendMask recvOut iha ihb =>
      have ha : rightShareOf sa y = (realShareOf (liftRightSeed sa x y) x y).2 :=
        rightShare_lift_eq sa x y
      have hb : rightShareOf sb y = (realShareOf (liftRightSeed sb x y) x y).2 :=
        rightShare_lift_eq sb x y
      have hshare :
          rightShareOf (RightObsSeed.and id sa sb sendMask recvOut) y =
            (realShareOf
                (RealSeed.and id (liftRightSeed sa x y) (liftRightSeed sb x y)
                  { fromLeft :=
                      bxor recvOut
                        ((realShareOf (liftRightSeed sa x y) x y).1 &&
                          (realShareOf (liftRightSeed sb x y) x y).2)
                    fromRight := sendMask })
                x y).2 := by
        simp [rightShareOf, realShareOf, andShareOT, ha, hb,
          leftToRightOTOutput_cancel]
      simpa [rightRealTrace, rightSimTrace, liftRightSeed, iha, ihb, ha, hb,
        leftToRightOTOutput_cancel] using
        congrArg
          (fun s =>
            RightTrace.and id
              (rightRealTrace (liftRightSeed sa x y) x y)
              (rightRealTrace (liftRightSeed sb x y) x y)
              s
              sendMask
              (bxor sendMask (realShareOf (liftRightSeed sa x y) x y).2)
              (realShareOf (liftRightSeed sb x y) x y).2
              recvOut)
          hshare

/-- 理想执行使用的总模拟种子。 -/
structure SimSeed {nLeft nRight : Nat} (w : Wire nLeft nRight) where
  real : RealSeed w
  left : LeftObsSeed w
  right : RightObsSeed w

/-- 真实协议的局部视图。 -/
def realProtocol (c : BoolCircuit) (input : Inputs c)
    (seed : RealSeed c.output) : LocalView PartyView :=
  fun p =>
    if p = left then
      PartyView.left ⟨leftRealTrace seed input.left input.right, F_SFE_BoolCircuit c input⟩
    else
      PartyView.right ⟨rightRealTrace seed input.left input.right, F_SFE_BoolCircuit c input⟩

/--
理想世界中的模拟器：

- 单边腐化时，使用对应的可观察种子；
- 双边腐化时，直接重放真实协议视图；
- 无腐化时，返回任意固定模拟视图即可。
-/
noncomputable def Simulator (c : BoolCircuit) :
    Corruption → Inputs c → Bool → SimSeed c.output → LocalView PartyView
  | corr, input, out, seed =>
      match corruptionCase corr with
      | .both => realProtocol c input seed.real
      | _ =>
          fun p =>
            if p = left then
              PartyView.left ⟨leftSimTrace seed.left input.left, out⟩
            else
              PartyView.right ⟨rightSimTrace seed.right input.right, out⟩

theorem left_case_perfect
    (c : BoolCircuit) (input : Inputs c) :
    PerfectSimulates (caseToCorruption .left)
      (RealExec (realProtocol c) input)
      (IdealExec (F_SFE_BoolCircuit c) (Simulator c) (caseToCorruption .left) input) := by
  ext obs
  constructor
  · intro hObs
    rcases hObs with ⟨seed, hObs⟩
    refine ⟨⟨seed, projectLeftSeed seed input.left input.right,
      projectRightSeed seed input.left input.right⟩, ?_⟩
    calc
      observedView (caseToCorruption .left)
          (IdealExec (F_SFE_BoolCircuit c) (Simulator c) (caseToCorruption .left) input
            ⟨seed, projectLeftSeed seed input.left input.right,
              projectRightSeed seed input.left input.right⟩)
          =
          observedView (caseToCorruption .left) (RealExec (realProtocol c) input seed) := by
            apply observedView_left_of_eq
            simp [RealExec, IdealExec, realProtocol, Simulator, leftTrace_project_eq]
      _ = obs := hObs
  · intro hObs
    rcases hObs with ⟨seed, hObs⟩
    refine ⟨liftLeftSeed seed.left input.left input.right, ?_⟩
    have hTrace :
        leftRealTrace (liftLeftSeed seed.left input.left input.right) input.left input.right =
          leftSimTrace seed.left input.left := by
      simpa using (leftTrace_lift_eq seed.left input.left input.right).symm
    calc
      observedView (caseToCorruption .left)
          (RealExec (realProtocol c) input (liftLeftSeed seed.left input.left input.right))
          =
          observedView (caseToCorruption .left)
            (IdealExec (F_SFE_BoolCircuit c) (Simulator c)
              (caseToCorruption .left) input seed) := by
            apply observedView_left_of_eq
            simp [RealExec, IdealExec, realProtocol, Simulator, hTrace]
      _ = obs := hObs

theorem right_case_perfect
    (c : BoolCircuit) (input : Inputs c) :
    PerfectSimulates (caseToCorruption .right)
      (RealExec (realProtocol c) input)
      (IdealExec (F_SFE_BoolCircuit c) (Simulator c) (caseToCorruption .right) input) := by
  ext obs
  constructor
  · intro hObs
    rcases hObs with ⟨seed, hObs⟩
    refine ⟨⟨seed, projectLeftSeed seed input.left input.right,
      projectRightSeed seed input.left input.right⟩, ?_⟩
    calc
      observedView (caseToCorruption .right)
          (IdealExec (F_SFE_BoolCircuit c) (Simulator c) (caseToCorruption .right) input
            ⟨seed, projectLeftSeed seed input.left input.right,
              projectRightSeed seed input.left input.right⟩)
          =
          observedView (caseToCorruption .right) (RealExec (realProtocol c) input seed) := by
            apply observedView_right_of_eq
            simp [RealExec, IdealExec, realProtocol, Simulator, rightTrace_project_eq]
      _ = obs := hObs
  · intro hObs
    rcases hObs with ⟨seed, hObs⟩
    refine ⟨liftRightSeed seed.right input.left input.right, ?_⟩
    have hTrace :
        rightRealTrace (liftRightSeed seed.right input.left input.right) input.left input.right =
          rightSimTrace seed.right input.right := by
      simpa using (rightTrace_lift_eq seed.right input.left input.right).symm
    calc
      observedView (caseToCorruption .right)
          (RealExec (realProtocol c) input (liftRightSeed seed.right input.left input.right))
          =
          observedView (caseToCorruption .right)
            (IdealExec (F_SFE_BoolCircuit c) (Simulator c)
              (caseToCorruption .right) input seed) := by
            apply observedView_right_of_eq
            simp [RealExec, IdealExec, realProtocol, Simulator, hTrace]
      _ = obs := hObs

theorem none_case_perfect
    (c : BoolCircuit) (input : Inputs c) :
    PerfectSimulates (caseToCorruption .none)
      (RealExec (realProtocol c) input)
      (IdealExec (F_SFE_BoolCircuit c) (Simulator c) (caseToCorruption .none) input) := by
  ext obs
  constructor <;> intro hObs
  · rcases hObs with ⟨seed, hEq⟩
    refine ⟨⟨seed, projectLeftSeed seed input.left input.right,
      projectRightSeed seed input.left input.right⟩, ?_⟩
    simpa [observedView_none] using hEq
  · rcases hObs with ⟨seed, hEq⟩
    refine ⟨seed.real, ?_⟩
    simpa [observedView_none] using hEq

theorem both_case_perfect
    (c : BoolCircuit) (input : Inputs c) :
    PerfectSimulates (caseToCorruption .both)
      (RealExec (realProtocol c) input)
      (IdealExec (F_SFE_BoolCircuit c) (Simulator c) (caseToCorruption .both) input) := by
  ext obs
  constructor
  · intro hObs
    rcases hObs with ⟨seed, hEq⟩
    refine ⟨⟨seed, projectLeftSeed seed input.left input.right,
      projectRightSeed seed input.left input.right⟩, ?_⟩
    simpa [RealExec, IdealExec, Simulator, corruptionCase_both]
      using hEq
  · intro hObs
    rcases hObs with ⟨seed, hEq⟩
    refine ⟨seed.real, ?_⟩
    simpa [RealExec, IdealExec, Simulator, corruptionCase_both]
      using hEq

/-- 通用的 real / ideal 视图等价定理。 -/
theorem gmw_real_ideal_view_eq
    (c : BoolCircuit) (corr : Corruption) (input : Inputs c) :
    PerfectSimulates corr
      (RealExec (realProtocol c) input)
      (IdealExec (F_SFE_BoolCircuit c) (Simulator c) corr input) := by
  have hCore := UCSecureMVP.of_cases
    (realProtocol c)
    (F_SFE_BoolCircuit c)
    (Simulator c)
    (none_case_perfect c)
    (left_case_perfect c)
    (right_case_perfect c)
    (both_case_perfect c)
  exact hCore corr input

/-- OT-hybrid 世界中 GMW 的 UC MVP 安全性。 -/
theorem gmw_ot_hybrid_uc_secure (c : BoolCircuit) :
    UCSecureMVP (realProtocol c) (F_SFE_BoolCircuit c) (Simulator c) := by
  refine UCSecureMVP.of_cases
    (realProtocol c)
    (F_SFE_BoolCircuit c)
    (Simulator c)
    (none_case_perfect c)
    (left_case_perfect c)
    (right_case_perfect c)
    (both_case_perfect c)

/-- 单个 XOR 门电路示例。 -/
def xorExample : BoolCircuit where
  nLeft := 1
  nRight := 1
  output := Wire.gate (Gate.xor 0 (Wire.inputL ⟨0, by decide⟩) (Wire.inputR ⟨0, by decide⟩))

/-- 单个 AND 门电路示例。 -/
def andExample : BoolCircuit where
  nLeft := 1
  nRight := 1
  output := Wire.gate (Gate.and 0 (Wire.inputL ⟨0, by decide⟩) (Wire.inputR ⟨0, by decide⟩))

/-- 一个小型混合电路示例。 -/
def mixedExample : BoolCircuit where
  nLeft := 2
  nRight := 1
  output :=
    Wire.gate
      (Gate.and 1
        (Wire.gate (Gate.xor 0 (Wire.inputL ⟨0, by decide⟩) (Wire.inputR ⟨0, by decide⟩)))
        (Wire.inputL ⟨1, by decide⟩))

theorem xorExample_eval (x y : Bool) :
    F_SFE_BoolCircuit xorExample
      { left := fun _ => x, right := fun _ => y } = bxor x y := by
  rfl

theorem andExample_eval (x y : Bool) :
    F_SFE_BoolCircuit andExample
      { left := fun _ => x, right := fun _ => y } = (x && y) := by
  rfl

theorem mixedExample_eval (x₀ x₁ y : Bool) :
    F_SFE_BoolCircuit mixedExample
      { left := fun i => if i.1 = 0 then x₀ else x₁, right := fun _ => y } =
      ((bxor x₀ y) && x₁) := by
  rfl

end LeanCryptoProtocols.GMW.OTHybrid

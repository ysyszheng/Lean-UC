import LeanCryptoProtocols.UC.Core
import LeanCryptoProtocols.Circuit.BoolCircuit

/-!
# 布尔电路安全函数计算理想功能

本文件给出一个可复用的两方布尔电路安全函数计算理想功能。

当前范围固定为：

- 公开布尔电路；
- 两方私有输入；
- 单输出；
- 静态腐化下对 simulator 的输入 / 输出裁剪接口。
-/

namespace LeanCryptoProtocols.UC.Functionality

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.Circuit

/-- 公开布尔电路上的安全函数计算值语义。 -/
def F_BoolCircuitSFE (c : BoolCircuit) : Inputs c → Bool :=
  c.eval

/-- 公开布尔电路上的安全函数计算理想功能。 -/
def IdealBoolCircuitSFE (c : BoolCircuit) : IdealFunctionality (Inputs c) Bool where
  eval := F_BoolCircuitSFE c
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

end LeanCryptoProtocols.UC.Functionality

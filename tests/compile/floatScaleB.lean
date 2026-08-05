module

import Init.Data.Float.Float32

/-!
Tests scaling non-finite floating-point values by large negative exponents.
-/

def hugeNegativeExponent : Int := -(2 ^ 70)
def hugePositiveExponent : Int := 2 ^ 70

public def main : IO Unit := do
  IO.println ((Float.inf.scaleB hugeNegativeExponent).isInf)
  IO.println (((-Float.inf).scaleB hugeNegativeExponent).isInf)
  IO.println ((Float.nan.scaleB hugeNegativeExponent).isNaN)
  IO.println (((-1.0 : Float).scaleB hugeNegativeExponent).toBits == (-0.0 : Float).toBits)
  IO.println (((-0.0 : Float).scaleB hugePositiveExponent).toBits == (-0.0 : Float).toBits)
  IO.println ((Float32.inf.scaleB hugeNegativeExponent).isInf)
  IO.println (((-Float32.inf).scaleB hugeNegativeExponent).isInf)
  IO.println ((Float32.nan.scaleB hugeNegativeExponent).isNaN)
  IO.println (((-1.0 : Float32).scaleB hugeNegativeExponent).toBits == (-0.0 : Float32).toBits)
  IO.println (((-0.0 : Float32).scaleB hugePositiveExponent).toBits == (-0.0 : Float32).toBits)

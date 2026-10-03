module

/-!
Tests scaling non-finite floating-point values by exponents too large for the native interface.
-/

def hugeNegativeExponent : Int := -(2 ^ 70)

#guard Float.inf.scaleB hugeNegativeExponent = Float.inf
#guard (-Float.inf).scaleB hugeNegativeExponent = -Float.inf
#guard Float.nan.scaleB hugeNegativeExponent = Float.nan
#guard (-1.0 : Float).scaleB hugeNegativeExponent = -0.0
#guard (-0.0 : Float).scaleB hugeNegativeExponent = -0.0

#guard Float32.inf.scaleB hugeNegativeExponent = Float32.inf
#guard (-Float32.inf).scaleB hugeNegativeExponent = -Float32.inf
#guard Float32.nan.scaleB hugeNegativeExponent = Float32.nan
#guard (-1.0 : Float32).scaleB hugeNegativeExponent = -0.0
#guard (-0.0 : Float32).scaleB hugeNegativeExponent = -0.0

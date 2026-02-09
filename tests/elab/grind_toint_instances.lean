module
open Lean.Grind

#synth ToInt.Add Nat (.ci 0)
variable (n : Nat) in
#synth ToInt.Add (Fin n) (.co 0 n)
#synth ToInt.Add UInt8 (.uint 8)
#synth ToInt.Add UInt16 (.uint 16)
#synth ToInt.Add UInt32 (.uint 32)
#synth ToInt.Add UInt64 (.uint 64)
#synth ToInt.Add USize (.uint System.Platform.numBits)
#synth ToInt.Add Int8 (.sint 8)
#synth ToInt.Add Int16 (.sint 16)
#synth ToInt.Add Int32 (.sint 32)
#synth ToInt.Add Int64 (.sint 64)
#synth ToInt.Add ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.Add (BitVec w) (.uint w)

#synth ToInt.Mul Nat (.ci 0)
variable (n : Nat) in
#synth ToInt.Mul (Fin n) (.co 0 n)
#synth ToInt.Mul UInt8 (.uint 8)
#synth ToInt.Mul UInt16 (.uint 16)
#synth ToInt.Mul UInt32 (.uint 32)
#synth ToInt.Mul UInt64 (.uint 64)
#synth ToInt.Mul USize (.uint System.Platform.numBits)
#synth ToInt.Mul Int8 (.sint 8)
#synth ToInt.Mul Int16 (.sint 16)
#synth ToInt.Mul Int32 (.sint 32)
#synth ToInt.Mul Int64 (.sint 64)
#synth ToInt.Mul ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.Mul (BitVec w) (.uint w)

#synth ToInt.OfNat Nat (.ci 0)
variable (n : Nat) [NeZero n] in
#synth ToInt.OfNat (Fin n) (.co 0 n)
#synth ToInt.OfNat UInt8 (.uint 8)
#synth ToInt.OfNat UInt16 (.uint 16)
#synth ToInt.OfNat UInt32 (.uint 32)
#synth ToInt.OfNat UInt64 (.uint 64)
#synth ToInt.OfNat USize (.uint System.Platform.numBits)
#synth ToInt.OfNat Int8 (.sint 8)
#synth ToInt.OfNat Int16 (.sint 16)
#synth ToInt.OfNat Int32 (.sint 32)
#synth ToInt.OfNat Int64 (.sint 64)
#synth ToInt.OfNat ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.OfNat (BitVec w) (.uint w)

#synth ToInt.Pow Nat (.ci 0)
variable (n : Nat) [NeZero n] in
#synth ToInt.Pow (Fin n) (.co 0 n)
#synth ToInt.Pow UInt8 (.uint 8)
#synth ToInt.Pow UInt16 (.uint 16)
#synth ToInt.Pow UInt32 (.uint 32)
#synth ToInt.Pow UInt64 (.uint 64)
#synth ToInt.Pow USize (.uint System.Platform.numBits)
#synth ToInt.Pow Int8 (.sint 8)
#synth ToInt.Pow Int16 (.sint 16)
#synth ToInt.Pow Int32 (.sint 32)
#synth ToInt.Pow Int64 (.sint 64)
#synth ToInt.Pow ISize (.sint System.Platform.numBits)
variable (w : Nat) [NeZero w] in
#synth ToInt.Pow (BitVec w) (.uint w)

-- No `Neg` instance for `Nat`. (But there is a `Sub` instance, below.)
variable (n : Nat) [NeZero n] in
#synth ToInt.Neg (Fin n) (.co 0 n)
#synth ToInt.Neg UInt8 (.uint 8)
#synth ToInt.Neg UInt16 (.uint 16)
#synth ToInt.Neg UInt32 (.uint 32)
#synth ToInt.Neg UInt64 (.uint 64)
#synth ToInt.Neg USize (.uint System.Platform.numBits)
#synth ToInt.Neg Int8 (.sint 8)
#synth ToInt.Neg Int16 (.sint 16)
#synth ToInt.Neg Int32 (.sint 32)
#synth ToInt.Neg Int64 (.sint 64)
#synth ToInt.Neg ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.Neg (BitVec w) (.uint w)

#synth ToInt.Sub Nat (.ci 0)
variable (n : Nat) [NeZero n] in
#synth ToInt.Sub (Fin n) (.co 0 n)
#synth ToInt.Sub UInt8 (.uint 8)
#synth ToInt.Sub UInt16 (.uint 16)
#synth ToInt.Sub UInt32 (.uint 32)
#synth ToInt.Sub UInt64 (.uint 64)
#synth ToInt.Sub USize (.uint System.Platform.numBits)
#synth ToInt.Sub Int8 (.sint 8)
#synth ToInt.Sub Int16 (.sint 16)
#synth ToInt.Sub Int32 (.sint 32)
#synth ToInt.Sub Int64 (.sint 64)
#synth ToInt.Sub ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.Sub (BitVec w) (.uint w)

#synth ToInt.Mod Nat (.ci 0)
variable (n : Nat) [NeZero n] in
#synth ToInt.Mod (Fin n) (.co 0 n)
#synth ToInt.Mod UInt8 (.uint 8)
#synth ToInt.Mod UInt16 (.uint 16)
#synth ToInt.Mod UInt32 (.uint 32)
#synth ToInt.Mod UInt64 (.uint 64)
#synth ToInt.Mod USize (.uint System.Platform.numBits)
-- No `Mod` instances for signed integers.
variable (w : Nat) [NeZero w] in
#synth ToInt.Mod (BitVec w) (.uint w)

#synth ToInt.Div Nat (.ci 0)
variable (n : Nat) [NeZero n] in
#synth ToInt.Div (Fin n) (.co 0 n)
#synth ToInt.Div UInt8 (.uint 8)
#synth ToInt.Div UInt16 (.uint 16)
#synth ToInt.Div UInt32 (.uint 32)
#synth ToInt.Div UInt64 (.uint 64)
#synth ToInt.Div USize (.uint System.Platform.numBits)
-- No `Div` instances for signed integers.
variable (w : Nat) [NeZero w] in
#synth ToInt.Div (BitVec w) (.uint w)

#synth ToInt.LE Nat (.ci 0)
variable (n : Nat) in
#synth ToInt.LE (Fin n) (.co 0 n)
#synth ToInt.LE UInt8 (.uint 8)
#synth ToInt.LE UInt16 (.uint 16)
#synth ToInt.LE UInt32 (.uint 32)
#synth ToInt.LE UInt64 (.uint 64)
#synth ToInt.LE USize (.uint System.Platform.numBits)
#synth ToInt.LE Int8 (.sint 8)
#synth ToInt.LE Int16 (.sint 16)
#synth ToInt.LE Int32 (.sint 32)
#synth ToInt.LE Int64 (.sint 64)
#synth ToInt.LE ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.LE (BitVec w) (.uint w)

#synth ToInt.LT Nat (.ci 0)
variable (n : Nat) in
#synth ToInt.LT (Fin n) (.co 0 n)
#synth ToInt.LT UInt8 (.uint 8)
#synth ToInt.LT UInt16 (.uint 16)
#synth ToInt.LT UInt32 (.uint 32)
#synth ToInt.LT UInt64 (.uint 64)
#synth ToInt.LT USize (.uint System.Platform.numBits)
#synth ToInt.LT Int8 (.sint 8)
#synth ToInt.LT Int16 (.sint 16)
#synth ToInt.LT Int32 (.sint 32)
#synth ToInt.LT Int64 (.sint 64)
#synth ToInt.LT ISize (.sint System.Platform.numBits)
variable (w : Nat) in
#synth ToInt.LT (BitVec w) (.uint w)

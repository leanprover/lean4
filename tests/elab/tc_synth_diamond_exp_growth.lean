/-!
# Exponential proof term growth in diamond-shaped TC synthesis

Regression test for https://github.com/leanprover/lean4/issues/13085.
Without the fix (lifting large intermediate answers into aux defs during synthesis),
this fails at depth ~7 with the default `synthInstance.maxSize` of 128 because the
proof term grows as 2^n in diamond-shaped instance dependency graphs.
-/

class T0 where u : Unit := ()
instance : T0 := {}

class L0 where u : Unit := ()
class R0 where u : Unit := ()
instance [T0] : L0 := {}
instance [T0] : R0 := {}

class T1 where u : Unit := ()
instance [L0] [R0] : T1 := {}

class L1 where u : Unit := ()
class R1 where u : Unit := ()
instance [T1] : L1 := {}
instance [T1] : R1 := {}

class T2 where u : Unit := ()
instance [L1] [R1] : T2 := {}

class L2 where u : Unit := ()
class R2 where u : Unit := ()
instance [T2] : L2 := {}
instance [T2] : R2 := {}

class T3 where u : Unit := ()
instance [L2] [R2] : T3 := {}

class L3 where u : Unit := ()
class R3 where u : Unit := ()
instance [T3] : L3 := {}
instance [T3] : R3 := {}

class T4 where u : Unit := ()
instance [L3] [R3] : T4 := {}

class L4 where u : Unit := ()
class R4 where u : Unit := ()
instance [T4] : L4 := {}
instance [T4] : R4 := {}

class T5 where u : Unit := ()
instance [L4] [R4] : T5 := {}

class L5 where u : Unit := ()
class R5 where u : Unit := ()
instance [T5] : L5 := {}
instance [T5] : R5 := {}

class T6 where u : Unit := ()
instance [L5] [R5] : T6 := {}

class L6 where u : Unit := ()
class R6 where u : Unit := ()
instance [T6] : L6 := {}
instance [T6] : R6 := {}

class T7 where u : Unit := ()
instance [L6] [R6] : T7 := {}

class L7 where u : Unit := ()
class R7 where u : Unit := ()
instance [T7] : L7 := {}
instance [T7] : R7 := {}

class T8 where u : Unit := ()
instance [L7] [R7] : T8 := {}

class L8 where u : Unit := ()
class R8 where u : Unit := ()
instance [T8] : L8 := {}
instance [T8] : R8 := {}

class T9 where u : Unit := ()
instance [L8] [R8] : T9 := {}

-- Depth 9 diamond: without the fix, would need synthInstance.maxSize ≈ 2^9 = 512+
-- With the fix, succeeds with the default maxSize of 128.
example : T9 := inferInstance

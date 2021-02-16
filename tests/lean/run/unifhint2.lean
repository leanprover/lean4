/- The following hints are too expensive, but good enough for small natural numbers -/
unif_hint natAddBase (x y : Nat) where
  y =?= 0
  |-
  Nat.add (Nat.succ x) y =?= Nat.succ x

unif_hint natAddStep (x y z w : Nat) where
  y =?= Nat.succ w
  z =?= Nat.add (Nat.succ x) w
  |-
  Nat.add (Nat.succ x) y =?= Nat.succ z

def BV (n : Nat) := { a : Array Bool // a.size = n }

def sext (x : BV s) (n : Nat) : BV (s+n) :=
  ⟨mkArray (s+n) false, Array.size_mkArray ..⟩

def bvmul (x y : BV w) : BV w := x

def tst1 (x y : BV 64) : BV 128 :=
  bvmul (sext x 64) (sext y _)

def tst2 (x y : BV 16) : BV 32 :=
  bvmul (sext x 16) (sext y _)

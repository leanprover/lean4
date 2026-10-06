module

/-! Polynomial casts and scalar multiplication in `Sym.Arith` (#15502). -/

open Lean.Grind

local instance : SMul Nat Int := Semiring.nsmul
local instance : SMul Int Rat := Ring.zsmul

register_sym_simp castArith where
  pre := arith >> control >> arrow_telescope
  post := ground

example (x : Int) (m n : Nat) : (m+n) • x = m • x + n • x := by sym => simp castArith
example (x : Int) (m n : Nat) : (m*n) • x = m • (n • x) := by sym => simp castArith
example (x : Rat) (m n : Int) : (m-n) • x = m • x - n • x := by sym => simp castArith
example (x : Rat) (m n : Int) : (m*n) • x = m • (n • x) := by sym => simp castArith

example (m n : Nat) : ((m+n : Nat) : Int) = (m : Int) + (n : Int) := by sym => simp castArith
example (m n : Int) : ((m*n : Int) : Rat) = (m : Rat) * (n : Rat) := by sym => simp castArith
example (m n : Int) : ((m-n : Int) : Rat) = (m : Rat) - (n : Rat) := by sym => simp castArith
example (m : Int) : ((-m : Int) : Rat) = -(m : Rat) := by sym => simp castArith
example (m : Nat) : ((m^3 : Nat) : Int) = (m : Int)^3 := by sym => simp castArith
example (m : Int) : ((m^3 : Int) : Rat) = (m : Rat)^3 := by sym => simp castArith
example (m n : Nat) : ((m*n+n^2 : Nat) : Rat) = (m : Rat)*(n : Rat)+(n : Rat)^2 := by
  sym => simp castArith
example (m n : Nat) : (((m+n : Nat) : Int) : Rat) = (m : Rat)+(n : Rat) := by
  sym => simp castArith

section
variable {R : Type} [CommSemiring R]
local instance : NatCast R := Semiring.natCast
local instance : SMul Nat R := Semiring.nsmul

example (m n : Nat) (x : R) : (m+n) • x = m • x + n • x := by sym => simp castArith
example (m n : Nat) : ((m*n+n^2 : Nat) : R) = (m : R)*(n : R)+(n : R)^2 := by
  sym => simp castArith

end

-- A normalized cast should be stable, including when it is the root.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (m n : Nat) (z : Int) : ((m+n : Nat) : Int) = z := by
  sym =>
    simp castArith
    simp castArith

-- Nat subtraction is truncated; nonstandard casts and operations are also atoms.
abbrev otherNatCast : NatCast Int := ⟨fun n => (n : Int) + 1⟩
abbrev otherNatAdd : HAdd Nat Nat Nat := ⟨fun m n => m+n+1⟩

example (m n : Nat) : True := by
  fail_if_success have : ((m-n : Nat) : Int) = (m : Int)-(n : Int) := by sym => simp castArith
  fail_if_success
    have : @NatCast.natCast Int otherNatCast (m+n) = (m : Int)+(n : Int) := by sym => simp castArith
  fail_if_success
    have : ((@HAdd.hAdd Nat Nat Nat otherNatAdd m n : Nat) : Int) = (m : Int)+(n : Int) := by sym => simp castArith
  trivial

example (m n : Nat) (x : Int) : ((m-n : Nat) : Int) + x = x + ((m-n : Nat) : Int) := by
  sym => simp castArith
example (m n : Nat) (x : Int) :
    @NatCast.natCast Int otherNatCast (m+n) + x = x + @NatCast.natCast Int otherNatCast (m+n) := by
  sym => simp castArith
example (m n : Nat) (x : Int) :
    ((@HAdd.hAdd Nat Nat Nat otherNatAdd m n : Nat) : Int) + x =
      x + ((@HAdd.hAdd Nat Nat Nat otherNatAdd m n : Nat) : Int) := by
  sym => simp castArith

section
variable {R : Type} [Semiring R]
local instance : NatCast R := Semiring.natCast
local instance : SMul Nat R := Semiring.nsmul

example (m n : Nat) (x : R) : (m+n) • x = m • x + n • x := by sym => simp castArith
example (m n : Nat) : ((m*n : Nat) : R) = ((n*m : Nat) : R) := by sym => simp castArith

end

-- A source operator may be heterogeneous even though its result is Nat.
abbrev otherNatIntAdd : HAdd Nat Int Nat := ⟨fun m n => m+n.toNat⟩
example (m : Nat) (n x : Int) :
    ((@HAdd.hAdd Nat Int Nat otherNatIntAdd m n : Nat) : Int) + x =
      x + ((@HAdd.hAdd Nat Int Nat otherNatIntAdd m n : Nat) : Int) := by
  sym => simp castArith

-- Casts also respect the target characteristic.
local instance : NatCast UInt8 := Semiring.natCast
example (m n : Nat) : ((m+256*n : Nat) : UInt8) = (m : UInt8) := by sym => simp castArith

example (m : Nat) : ((2*m+3 : Nat) : Int) = 2*(m : Int)+3 := by sym => simp castArith
example (m n : Int) : ((m-2*n : Int) : Rat) = (m : Rat)-2*(n : Rat) := by sym => simp castArith

-- Non-polynomial source operations remain atoms.
example (m k : Nat) (x : Int) : ((m^k : Nat) : Int)+x = x+((m^k : Nat) : Int) := by
  sym => simp castArith
example (m n : Int) (x : Rat) : ((m/n : Int) : Rat)+x = x+((m/n : Int) : Rat) := by
  sym => simp castArith
example (m n : Int) (x : Rat) : ((m%n : Int) : Rat)+x = x+((m%n : Int) : Rat) := by
  sym => simp castArith

section
variable {R : Type} [Ring R]
local instance : IntCast R := Ring.intCast
local instance : SMul Int R := Ring.zsmul

example (m n : Int) : ((m*n : Int) : R) = ((n*m : Int) : R) := by sym => simp castArith
example (m n : Int) (x : R) : (m-n) • x = m • x - n • x := by sym => simp castArith

end

-- Cast rewriting still applies when the enclosing polynomial exceeds the degree budget.
example (m n : Nat) : (((m+n : Nat) : Int))^65 = ((m : Int)+(n : Int))^65 := by
  sym => simp castArith

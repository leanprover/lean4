import Lean

/-!
Normalization of powers with symbolic `Nat` exponents in `Sym.Arith` (`symbolicPow := true`):
sums and numeral coefficients in exponents, powers of products, and powers of powers, as Mathlib's
`ring` treats them. These are the goals of #15480 that `grind` does not prove.
-/

open Lean Meta Elab Tactic Sym

elab "power_nf" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      Simp.SimpM.run' (Simp.simp (← shareCommon target))
        { pre := Simp.simpArith (symbolicPow := true), post := Simp.evalGround }
    match r with
    | .step t h .. =>
      unless t.isTrue do throwError "unequal normal forms:{indentExpr t}"
      g.assign (← mkOfEqTrue h)
    | .rfl .. => throwError "no progress"
    replaceMainGoal []

open Lean.Grind

example (x : Int) (n : Nat) : x^(n+n) = (x^n)^2 := by
  power_nf

example (x : Int) (m n : Nat) : x^(2*m+3*n+1) = (x^m)^2*(x^n)^3*x := by
  power_nf

example (x : Int) (m n : Nat) : x^(m*n) = x^(n*m) := by
  power_nf

example (x : Int) (m n : Nat) : x^((m+n)^3) = x^(m^3+3*m^2*n+3*m*n^2+n^3) := by
  power_nf

example {R : Type} [CommSemiring R] (x : R) (m n : Nat) : (x^m)^n = x^(m*n) := by
  power_nf

example (x : Int) (m n k : Nat) : ((x^m)^n)^k = x^(m*n*k) := by
  power_nf

example (x : Rat) (m n : Nat) : (x^(m+1))^n = x^(n*(m+1)) := by
  power_nf

example (x : Int) (m n : Nat) : (x^(m+1))^(n+2) = x^(m*n+2*m+n+2) := by
  power_nf

example (x y : Int) (m n : Nat) : ((x+y)^m)^n = (x+y)^(m*n) := by
  power_nf

example (x : Int) (n : Nat) : (x^2)^n = x^(2*n) := by
  power_nf

example (x : Int) (n : Nat) : (x^n)^3 = x^(3*n) := by
  power_nf

example (x : Int) (m n k : Nat) : (x^(m+n))^k = x^(m*k)*x^(n*k) := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (n : Nat) : (x*y)^n = x^n*y^n := by
  power_nf

example (x y z : Nat) (n : Nat) : (x*y*z)^n = x^n*y^n*z^n := by
  power_nf

example (x : Int) (n : Nat) : ((2 : Int)*x)^n = (2 : Int)^n*x^n := by
  power_nf

example (x y : Int) (m n k : Nat) : (x^m*y^k)^n = x^(m*n)*y^(k*n) := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (n : Nat) : (x*y)^(n+2) = x^n*y^n*x^2*y^2 := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (m n : Nat) : ((x*y)^m)^n = x^(m*n)*y^(m*n) := by
  power_nf

example (x y : Int) (n : Nat) : ((x+y)^2)^n = (x^2+2*x*y+y^2)^n := by
  power_nf

example (x y : Int) (m n : Nat) : (x*y+y*x)^(m+n) = (2*x*y)^m*(2*x*y)^n := by
  power_nf

example (x y : Int) (m n : Nat) : (x^n+y^m)^2 = x^(2*n)+2*x^n*y^m+y^(2*m) := by
  power_nf

example (x y : Rat) (m n : Nat) : (x^n+y^m)^3 = x^(3*n)+3*x^(2*n)*y^m+3*x^n*y^(2*m)+y^(3*m) := by
  power_nf

example {R : Type} [CommSemiring R] (x y : R) (m n : Nat) : (2*x^n+3*y^m)^2 = 4*x^(2*n)+12*x^n*y^m+9*y^(2*m) := by
  power_nf

example (x y : Int) (m n : Nat) : (x^n+y^m)*(x^n-y^m) = x^(2*n)-y^(2*m) := by
  power_nf

example (m n : Nat) : (0 : Int)^((m+1)*(n+1)) = 0 := by
  power_nf

example (m n : Nat) : ((2 : Int)^m)^n = (2 : Int)^(m*n) := by
  power_nf

example (x : Rat) (n : Nat) : (x/2)^n = x^n*(1/2 : Rat)^n := by
  power_nf

example (x y : Rat) (m n : Nat) : (x^n/2+y^m/3)^2 = x^(2*n)/4+x^n*y^m/3+y^(2*m)/9 := by
  power_nf

example (x : Int) (n : Nat) : x^(2^(n+1)) = (x^(2^n))^2 := by
  power_nf

example {R : Type} [CommSemiring R] (x : R) (n : Nat) : x = x*1^n := by
  power_nf

-- `0 ^ n` is not `0` when `n = 0`.
example : True := by
  fail_if_success have : ∀ (n : Nat), (0 : Int)^n = 0 := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (n : Nat), (0 : Rat)^n = 0 := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Int) (m n : Nat), x^(m+n) = x^m+x^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Rat) (m n : Nat), x^(m+n) = x^m+x^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x y : Int) (n : Nat), (x+y)^n = x^n+y^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x y : Rat) (n : Nat), (x+y)^n = x^n+y^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Int) (m n : Nat), (x^m)^n = x^(m+n) := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ (x : Rat) (m n : Nat), (x^m)^n = x^(m+n) := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ {R : Type} [Lean.Grind.Semiring R] (x y : R) (n : Nat), (x*y)^n = x^n*y^n := by intros; power_nf
  trivial

example : True := by
  fail_if_success have : ∀ {R : Type} [Lean.Grind.Semiring R] (x y : R), x*y = y*x := by intros; power_nf
  trivial

-- In a noncommutative ring, exponents are split but powers of products are atoms.
example {R : Type} [Ring R] (x : R) (n : Nat) : x^(n+1) = x^n * x := by
  power_nf

example {R : Type} [Ring R] (x : R) (m n : Nat) : (x^m)^(2*n) = x^(m*n) * x^(n*m) := by
  power_nf

example {R : Type} [Ring R] (x y : R) (n : Nat) : (x*y)^(n+1) = (x*y)^n * (x*y) := by
  power_nf

example : True := by
  fail_if_success have : ∀ {R : Type} [Ring R] (x y : R) (n : Nat), (x*y)^n = x^n*y^n := by intros; power_nf
  trivial

-- Symbolic powers inside other terms.
example (f : Int → Int) (x : Int) (n : Nat) : f (x^(n+1) - x * x^n) = f 0 := by
  power_nf

-- A power with another instance is not interpreted.
example (x : Int) (n : Nat) :
    letI : HPow Int Nat Int := ⟨fun x _ => x⟩
    x ^ (n + 1) = x → x ^ (n + 1) = x := by
  intro h
  fail_if_success power_nf
  exact h

-- A numeral coefficient anywhere in an exponent monomial.
example (x : Int) (m n : Nat) : x^(m*2*n) = (x^(m*n))^2 := by
  power_nf

-- Exponents of other types are atoms (no loop through `simp`).
instance : HPow Int Bool Int := ⟨fun x b => if b then x else 1⟩
example (x : Int) (b : Bool) : x ^ b + x ^ b = 2 * x ^ b := by
  power_nf

-- Powers of the same base are not commuted in a noncommutative ring.
example : True := by
  fail_if_success have : ∀ {R : Type} [Ring R] (x : R) (n : Nat), x * x^n = x^n * x := by intros; power_nf
  trivial

-- Over `sym.arith.maxDegree`, a power is an atom with its base normalized.
set_option sym.arith.maxDegree 2 in
example (x : Int) (n : Nat) : x^(n+3) = x^(n+3) := by
  power_nf

elab "power_nf_nodistrib" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let r ← SymM.run do
      Simp.SimpM.run' (Simp.simp (← shareCommon target))
        { pre := Simp.simpArith (distrib := false) (symbolicPow := true), post := Simp.evalGround }
    let .step t h .. := r | throwError "no progress"
    unless t.isTrue do throwError "unequal normal forms:{indentExpr t}"
    g.assign (← mkOfEqTrue h)
    replaceMainGoal []

-- With `distrib := false`, a power of a sum is not expanded, but its exponent is still split.
example (x y : Int) (n : Nat) : (x+y)^(n+2) = (y+x)^n * (x+y)^2 := by
  power_nf_nodistrib

example (x y : Int) (n : Nat) : (x*y)^(2*n) = (x^n)^2 * (y^n)^2 := by
  power_nf_nodistrib

import Lean

/-!
Tests for `[grind homo]` attribute registration. Homomorphism rules are registered in a
`Sym.simp` theorem set retrievable via `Lean.Meta.Grind.getHomoTheorems`.
-/

open Lean Meta Grind

/-- Custom source type so this test is independent of the `[grind homo]` rules in `Init`. -/
structure W where
  val : Int

instance : Add W := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Mul W := ⟨fun a b => ⟨a.val * b.val⟩⟩

def wu (x : W) : Int := x.val

axiom wu_add (x y : W) : wu (x + y) = (wu x + wu y) % 2^32
axiom wu_mul (x y : W) : wu (x * y) = (wu x * wu y) % 2^32
axiom wu_eq (x y : W) : (x = y) ↔ (wu x = wu y)

attribute [grind homo] wu_add
attribute [grind homo] wu_mul
attribute [grind homo] wu_eq

/-- Displays the `[grind homo]` rules matching `wu (x + x)` and `x = x`. -/
def checkMatches : MetaM Unit := do
  withLocalDeclD `x (mkConst ``W) fun x => do
    let thms ← getHomoTheorems
    let add ← mkAppM ``wu #[← mkAppM ``HAdd.hAdd #[x, x]]
    for thm in thms.getMatch add do
      logInfo m!"{thm.expr}"
    let eq ← mkEq x x
    for thm in thms.getMatch eq do
      logInfo m!"{thm.expr}"

/--
info: wu_add
---
info: fun x y => propext (wu_eq x y)
-/
#guard_msgs in
run_meta checkMatches

/-- error: homomorphism rules must be set using the default `[grind]` attribute -/
#guard_msgs in
attribute [lia homo] wu_add

axiom bad : Nat

/--
error: Cannot add `grind homo` attribute to `bad`: It is not a proposition nor a definition with equation theorems.
-/
#guard_msgs in
attribute [grind homo] bad

/--
error: homomorphism rules should be registered using the `@[grind homo]` attribute
-/
#guard_msgs in
example : True := by grind [homo wu_add]

/-! Conditional theorems are rejected: hypotheses that must be discharged are not
supported. Hypotheses occurring in the conclusion (instantiated by matching) are fine. -/

axiom wu_cond (x y : W) (h : wu x = 0) : wu (x + y) = wu y

/--
error: invalid `[grind homo]` theorem, `wu_cond` is conditional: hypothesis
  wu x = 0
is not determined by the left-hand side and would have to be discharged when the rule is applied. Homomorphism rules must be unconditional; use E-matching attributes such as `[grind =]` or `[grind →]` for conditional theorems
-/
#guard_msgs in
attribute [grind homo] wu_cond

def wcast (_h : True) (x : W) : W := x

axiom wu_wcast (h : True) (x : W) : wu (wcast h x) = wu x

#guard_msgs in
attribute [grind homo] wu_wcast

/-! An instance-implicit parameter not occurring in the left-hand side is fine: it is
synthesized during rewriting. In particular, `Prop`-valued instances such as `NeZero`
must not be reported as conditional hypotheses. -/

def wofNat (n : Nat) : W := ⟨n⟩

axiom wu_ofNat (n : Nat) [NeZero n] : wu (wofNat n) = (n : Int)

#guard_msgs in
attribute [grind homo] wu_ofNat

/-! A parameter occurring only in the right-hand side cannot be instantiated. -/

axiom wu_rhs (x y : W) : wu x = wu (x + y)

/--
error: invalid `[grind homo]` theorem, parameter `y` of `wu_rhs` is not determined by the left-hand side of the rule
-/
#guard_msgs in
attribute [grind homo] wu_rhs

/-! `reset_grind_attrs%` clears the homo extension. -/

reset_grind_attrs%

#guard_msgs in
run_meta checkMatches

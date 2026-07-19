import Lean

/-!
Tests for `[grind homo]` attribute registration. Homomorphism rules are registered in a
`Sym.simp` theorem set retrievable via `Lean.Meta.Grind.getHomoTheorems`.
-/

open Lean Meta Grind

def wu (x : BitVec 32) : Int := (x.toNat : Int)

axiom wu_add (x y : BitVec 32) : wu (x + y) = (wu x + wu y) % 2^32
axiom wu_mul (x y : BitVec 32) : wu (x * y) = (wu x * wu y) % 2^32
axiom wu_eq (x y : BitVec 32) : (x = y) ↔ (wu x = wu y)

attribute [grind homo] wu_add
attribute [grind homo] wu_mul
attribute [grind homo] wu_eq

/-- Displays the `[grind homo]` rules matching `wu (x + x)` and `x = x`. -/
def checkMatches : MetaM Unit := do
  withLocalDeclD `x (mkApp (mkConst ``BitVec) (mkNatLit 32)) fun x => do
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

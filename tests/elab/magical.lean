import Lean
/-!
# The kernel does not allow primitive projections on propositions

This test is adapted from the test introduced in commits
7920db952116e838b31c6f59f17bde0af01df545 and 3746005f5fc35d030d26ced2f7bcaabc295224c2,
and which was removed in #8986 because the elaborator is better at rejecting them.
In this version, we do direct tests of the kernel.
-/

open Lean Meta

set_option pp.proofs true

/-!
Projection to the witness should be rejected.

This test is creating the declaration
```
def test.witness : Nat := (Exists.intro 0 True.intro : ∃ x : Nat, True).1
```
-/
/--
error: (kernel) invalid projection
  (Exists.intro Nat.zero True.intro).1
-/
#guard_msgs in
#eval do
  addDecl <| .defnDecl {
    name := `test.witness
    levelParams := []
    type := mkConst `Nat
    hints := .abbrev
    safety := .safe
    value :=
      mkProj ``Exists 0 <|
        mkApp4 (mkConst ``Exists.intro [levelOne])
          (mkConst ``Nat)
          (mkLambda `x .default (mkConst ``Nat) (mkConst ``True))
          (mkConst ``Nat.zero)
          (mkConst ``True.intro)
  }

/-!
`Subtype` version is accepted. (This is to check that the expression above was constructed correctly.)
-/
#guard_msgs in
#eval do
  addDecl <| .defnDecl {
    name := `test.witness'
    levelParams := []
    type := mkConst `Nat
    hints := .abbrev
    safety := .safe
    value :=
      mkProj ``Subtype 0 <|
        mkApp4 (mkConst ``Subtype.mk [levelOne])
          (mkConst ``Nat)
          (mkLambda `x .default (mkConst ``Nat) (mkConst ``True))
          (mkConst ``Nat.zero)
          (mkConst ``True.intro)
  }

/-!
Projection to the property should be rejected as well (it could contain the witness projection).

This test is creating the declaration
```
theorem test.witness_eq (h : ∃ x : Nat, True) : h.2 = h.2 := rfl
```
-/
/--
error: (kernel) invalid projection
  h.2
-/
#guard_msgs in
#eval do
  addDecl <| .thmDecl {
    name := `test.witness_eq
    levelParams := []
    type :=
      mkForall `h .default
        (mkApp2 (mkConst ``Exists [levelOne]) (mkConst ``Nat) (mkLambda `x .default (mkConst ``Nat) (mkConst ``True)))
        (mkApp3 (mkConst ``Eq [levelZero])
          (mkConst ``True)
          (mkProj ``Exists 1 (mkBVar 0))
          (mkProj ``Exists 1 (mkBVar 0)))
    value := mkLambda `h .default
      (mkApp2 (mkConst ``Exists [levelOne]) (mkConst ``Nat) (mkLambda `x .default (mkConst ``Nat) (mkConst ``True)))
      (mkApp2 (mkConst ``Eq.refl [levelZero]) (mkConst ``True) (mkProj ``Exists 1 (mkBVar 0)))
  }

/-!
`Subtype` version is accepted. (This is to check that the expression above was constructed correctly.)
-/
#guard_msgs in
#eval do
  addDecl <| .thmDecl {
    name := `test.witness_eq'
    levelParams := []
    type :=
      mkForall `h .default
        (mkApp2 (mkConst ``Subtype [levelOne]) (mkConst ``Nat) (mkLambda `x .default (mkConst ``Nat) (mkConst ``True)))
        (mkApp3 (mkConst ``Eq [levelZero])
          (mkConst ``True)
          (mkProj ``Subtype 1 (mkBVar 0))
          (mkProj ``Subtype 1 (mkBVar 0)))
    value := mkLambda `h .default
      (mkApp2 (mkConst ``Subtype [levelOne]) (mkConst ``Nat) (mkLambda `x .default (mkConst ``Nat) (mkConst ``True)))
      (mkApp2 (mkConst ``Eq.refl [levelZero]) (mkConst ``True) (mkProj ``Subtype 1 (mkBVar 0)))
  }

import Lean

/-!
This test checks that we can enter, typecheck etc. terms that are only type-correct at
transparency `all`.
-/

open Lean Meta


def T := Nat → Nat
def x : T := fun n => n + 1

-- All well:
def n1 : Nat := x 1


-- Now we make `T` irreducible. A bunch of things should break:

attribute [irreducible] T

/--
error: function expected at
  x
term has type
  T
-/
#guard_msgs in
def n2 : Nat := x 1


-- NB: Checking does not break! Always done at transparency `all`.
run_meta do
  Meta.check (.app (mkConst ``x) (mkNatLit 1))

-- Type inference fails:

/--
error: function expected
  x 1
-/
#guard_msgs in
run_meta do
  let _ ← Meta.inferType (.app (mkConst ``x) (mkNatLit 1))

-- But succeeds at transparency .all

run_meta do
  withTransparency .all do
    let _ ← Meta.inferType (.app (mkConst ``x) (mkNatLit 1))

-- An elaborator that sets transparency to .all:

elab "with_unfolding_all" t:term : term <= expectedType? =>
  withTransparency .all <|
    Elab.Term.elabTerm t expectedType?

/--
error: function expected
  x 1
-/
#guard_msgs in
def n3 : Nat := with_unfolding_all x 1

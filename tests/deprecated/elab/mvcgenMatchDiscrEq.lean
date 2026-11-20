import Std.Tactic.Do

set_option sym.debug true

/-!
Regression test for #12275 with the deprecated `mvcgen +jp`: splitting a `match h : d with` must
not substitute the discriminant in the alternatives, since the alternative's body is only
well-typed because the let-bound discriminant unfolds to its value. The `vcgen` version of this
test is `tests/elab/vcgenMatchDiscrEq.lean`.
-/

def f (_ : Unit) : Bool := true
def foo (_hxy : f () = true) : Nat := 1

def minPathProg : Id Nat := do
  let bla := f ()
  match h : bla with
  | true => return foo h
  | false => return 0

open Std.Do

def minPath : Nat := Id.run minPathProg

example : minPath = 1 := by
  generalize hwp : minPath = wp
  apply Id.of_wp_run_eq hwp
  unfold minPathProg
  mvcgen +jp
  all_goals simp_all [foo, f]

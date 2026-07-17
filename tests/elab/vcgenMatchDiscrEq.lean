import Std.Tactic.Do
import Std.Internal.Do

/-!
Regression test for `vcgen` splitting a `match h : d with` whose alternatives bind an equality
`h : d = pattern`. The split must not substitute the discriminant in the alternatives, since their
types mention it; each verification condition instead carries the equality hypothesis.
Includes the example from issue #12275, where the alternative's body is only well-typed because
the let-bound discriminant unfolds to its value.
-/

set_option mvcgen.warning false

def dep (n : Option Nat) : Id Nat :=
  match _h : n with | some y => pure (y + 1) | none => pure 2

/-- Annotated and plain discriminants mixed, in a stateful monad. -/
def mixed (n m : Option Nat) : StateM Nat Unit := do
  match _h : n, m with
  | some y, some z => set (y + z)
  | _, _ => pure ()

/-- Every discriminant annotated. -/
def both (n m : Option Nat) : Id Nat :=
  match _h1 : n, _h2 : m with
  | some y, some z => pure (y + z + 1)
  | _, _ => pure 1

section
open Lean.Order Std.Internal.Do

example (n : Option Nat) : ⦃ True ⦄ dep n ⦃ fun r => r > 0 ⦄ := by
  vcgen [dep.eq_def] with finish

example (n m : Option Nat) : ⦃ fun _ => True ⦄ mixed n m ⦃ fun _ _ => True ⦄ := by
  vcgen [mixed.eq_def] with finish

example (n m : Option Nat) : ⦃ True ⦄ both n m ⦃ fun r => r > 0 ⦄ := by
  vcgen [both.eq_def] with finish

end

/-!
Issue #12275: the alternative's body is only well-typed because the let-bound discriminant
unfolds to its value, so the discriminant must not be substituted during the split.
-/

def f (_ : Unit) : Bool := true
def foo (_hxy : f () = true) : Nat := 1

def minPathProg : Id Nat := do
  let bla := f ()
  match h : bla with
  | true => return foo h
  | false => return 0

section
open Lean.Order Std.Internal.Do

example : ⦃ True ⦄ minPathProg ⦃ fun r => r ≤ 1 ⦄ := by
  vcgen [minPathProg] with finish [foo]

end

section
open Std.Do

def minPath : Nat := Id.run minPathProg

example : minPath = 1 := by
  generalize hwp : minPath = wp
  apply Id.of_wp_run_eq hwp
  unfold minPathProg
  mvcgen +jp
  all_goals simp_all [foo, f]

end

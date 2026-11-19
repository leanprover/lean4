import Lean
/-!
The proof of an equation for a `match` on `String` literals skips the tests for the preceding
literals with `dite_eq_of_not`. The proof for the remaining tests is under a binder, like the
remaining tests in the matcher, so the two share their subterms. With `dite_eq_right`, every
skipped test added a copy of the remaining tests to the proof (#16313).
-/
open Lean Meta

def f : String → Nat
  | "a" => 0
  | "b" => 1
  | "c" => 2
  | _ => 3

/--
info: theorem f.match_1.congr_eq_3.{u_1} : ∀ (motive : String → Sort u_1) (x : String) (h_1 : Unit → motive "a")
  (h_2 : Unit → motive "b") (h_3 : Unit → motive "c") (h_4 : (x : String) → motive x),
  x = "c" →
    (match x with
      | "a" => h_1 ()
      | "b" => h_2 ()
      | "c" => h_3 ()
      | x => h_4 x) ≍
      h_3 () :=
fun motive x h_1 h_2 h_3 h_4 heq_1 =>
  Eq.symm heq_1 ▸
    id
      (heq_of_eq
        (dite_eq_of_not (id (String.Internal.ofList_ne_ofList ['c'] ['a'] 0 (Eq.refl false))) fun h =>
          dite_eq_of_not (id (String.Internal.ofList_ne_ofList ['c'] ['b'] 0 (Eq.refl false))) fun h =>
            Eq.trans (dite_eq_left (Eq.refl "c")) (id (Eq.refl (h_3 ())))))
-/
#guard_msgs in
set_option pp.proofs true in
#print f.match_1.congr_eq_3

/-!
The size added to the proof by each skipped test does not depend on the number of tests that
follow it. `short` and `long` start with the same 8 literals. So, the difference between the sizes
of the proofs of `congr_eq_i` and `congr_eq_(i+1)` is the same for both, for `i < 7`.
The last literal of `short` is not compared: its test is followed by the catch-all in `short`,
and by another test in `long`.
-/

def short : String → Nat
  | "a0" => 0 | "a1" => 1 | "a2" => 2 | "a3" => 3 | "a4" => 4 | "a5" => 5 | "a6" => 6 | "a7" => 7
  | _ => 100

def long : String → Nat
  | "a0" => 0 | "a1" => 1 | "a2" => 2 | "a3" => 3 | "a4" => 4 | "a5" => 5 | "a6" => 6 | "a7" => 7
  | "b0" => 0 | "b1" => 1 | "b2" => 2 | "b3" => 3 | "b4" => 4 | "b5" => 5 | "b6" => 6 | "b7" => 7
  | _ => 100

/-- Returns the sizes of the proofs of the first 7 congruence equations of `matcherName`. -/
def proofSizes (matcherName : Name) : MetaM (Array Nat) := do
  let eqns ← Match.genMatchCongrEqns matcherName
  eqns[*...7].toArray.mapM fun eqn => do
    let some (.thmInfo info) := (← getEnv).find? eqn | throwError "theorem expected: {eqn}"
    if (info.value.find? (·.isConstOf ``dite_eq_right)).isSome then
      throwError "unexpected `dite_eq_right` in the proof of {eqn}"
    (ShareCommon.shareCommon' info.value).numObjs

run_meta do
  let shortSizes ← proofSizes ``short.match_1
  let longSizes ← proofSizes ``long.match_1
  for i in *...6 do
    unless shortSizes[i+1]! - shortSizes[i]! == longSizes[i+1]! - longSizes[i]! do
      throwError "proof size depends on the number of remaining tests: {shortSizes} {longSizes}"

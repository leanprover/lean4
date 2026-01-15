/-
This is from Markus's blog post on monadic reasoning:
https://markushimmel.de/blog/my-first-verified-imperative-program/
-/

import Std.Data.HashSet.Lemmas
import Std.Tactic.Do

open Std Do

/-!
# Missing standard library material that will be part of a future Lean release
-/

namespace List

theorem exists_mem_iff_exists_getElem (P : α → Prop) (l : List α) :
    (∃ x ∈ l, P x) ↔ ∃ (i : Nat), ∃ hi, P (l[i]'hi) := by
  grind [mem_iff_getElem]

/--
`l.ExistsPair P` asserts that there are indices `i` and `j` such that `i < j` and `P l[i] l[j]` is true.
-/
structure ExistsPair (P : α → α → Prop) (l : List α) where
  not_pairwise : ¬l.Pairwise (¬P · ·)

theorem existsPair_iff_not_pairwise {P : α → α → Prop} {l : List α} :
    l.ExistsPair P ↔ ¬l.Pairwise (fun x y => ¬P x y) := by
  grind [ExistsPair]

@[simp, grind]
theorem not_existsPair_nil {P : α → α → Prop} : ¬[].ExistsPair P := by
  simp [existsPair_iff_not_pairwise]

@[simp, grind]
theorem existsPair_cons {P : α → α → Prop} {x : α} {xs : List α} :
    (x::xs).ExistsPair P  ↔ (∃ y ∈ xs, P x y) ∨ xs.ExistsPair P := by
  grind [List.existsPair_iff_not_pairwise, pairwise_iff_forall_sublist]

@[simp, grind]
theorem existsPair_append {P : α → α → Prop} {xs ys : List α} :
    (xs ++ ys).ExistsPair P ↔ xs.ExistsPair P ∨ ys.ExistsPair P ∨ (∃ x ∈ xs, ∃ y ∈ ys, P x y) := by
  grind [List.existsPair_iff_not_pairwise]

end List

-- Tell Lean that it doesn't need to warn us that `mvcgen` is still a pre-release.
set_option mvcgen.warning false

/-!
# Imperative implementation
-/

def pairsSumToZero (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅

  for x in l do
    if -x ∈ seen then
      return true
    seen := seen.insert x

  return false

/-!
# Verification of imperative implementation
-/

theorem pairsSumToZero_correct (l : List Int) : pairsSumToZero l ↔ l.ExistsPair (fun a b => a + b = 0) := by
  generalize h : pairsSumToZero l = r
  apply Id.of_wp_run_eq h

  mvcgen

  case inv1 =>
    exact Invariant.withEarlyReturn
      (onReturn := fun r b => ⌜r = true ∧ l.ExistsPair (fun a b => a + b = 0)⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ ¬traversalState.prefix.ExistsPair (fun a b => a + b = 0)⌝)

  all_goals simp_all <;> grind

/--
trace: l : List Int
⊢ (match
          (forIn l ⟨none, ∅⟩ fun x r =>
                if -x ∈ r.snd then pure (ForInStep.done ⟨some true, r.snd⟩)
                else pure (ForInStep.yield ⟨none, r.snd.insert x⟩)).run.fst with
        | none => pure false
        | some a => pure a).run =
      true ↔
    List.ExistsPair (fun a b => a + b = 0) l
---
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem pairsSumToZero_correct_directly (l : List Int) : pairsSumToZero l ↔ l.ExistsPair (fun a b => a + b = 0) := by
  simp [pairsSumToZero]
  trace_state
  -- give up; need lemma about `forIn`
  admit

namespace Functional

/-!
# Bonus: functional implementation
-/

def pairsSumToZero (l : List Int) : Bool :=
  go l ∅
where
  go (m : List Int) (seen : HashSet Int) : Bool :=
    match m with
    | [] => false
    | x::xs => if -x ∈ seen then true else go xs (seen.insert x)

/-!
# Bonus: verification of functional implementation
-/

theorem pairsSumToZero_go_iff (l : List Int) (seen : HashSet Int) :
    pairsSumToZero.go l seen = true ↔
      l.ExistsPair (fun a b => a + b = 0) ∨ ∃ a ∈ seen, ∃ b ∈ l, a + b = 0 := by
  fun_induction pairsSumToZero.go <;> simp_all <;> grind

theorem pairsSumToZero_iff (l : List Int) :
    pairsSumToZero l = true ↔ l.ExistsPair (fun a b => a + b = 0) := by
  simp [pairsSumToZero, pairsSumToZero_go_iff]

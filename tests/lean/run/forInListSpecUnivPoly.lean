import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false
set_option warn.sorry false

def BubbleSort {α} [LT α] [DecidableLT α] (a: Array α) : Array α := Id.run do
  let n := a.size
  let mut a : Vector α n := a.toVector
  for i in List.range (n - 1) do
    for hj : j in List.range (n - i - 1) do
      have := List.mem_range.mp hj
      if a[j] > a[j + 1] then
        a := a.swap j (j+1)
  return a.toArray

theorem BubbleSortSameElements [LT α] [DecidableLT α] (A : Array α) : List.Perm A.toList (BubbleSort A).toList := by
  generalize h : BubbleSort A = x
  apply Id.of_wp_run_eq h
  set_option trace.Elab.Tactic.Do.spec true in
  mvcgen
  -- This should be able to apply the universe polymorphic Spec.forIn_list so that we get to
  -- provide invariant goals below. Back when the spec wasn't sufficiently universe polymorphic,
  -- the defeq check after instantiation used to fail for this program, because the level of `Nat`
  -- was not the same as the level of `α`.
  case inv1 => sorry
  case inv2 => sorry
  all_goals sorry

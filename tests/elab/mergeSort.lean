open List MergeSort Internal

-- If we omit the comparator, it is filled by the autoparam `fun a b => a ≤ b`
example : mergeSort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  by native_decide

example : mergeSort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] (· ≤ ·) = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  by native_decide

example : mergeSort [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] (fun x y => x/10 ≤ y/10) = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  by native_decide

example : mergeSortTR [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  by native_decide

example : mergeSortTR [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] (fun x y => x/10 ≤ y/10) = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  by native_decide

example : mergeSortTR₂ [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  by native_decide

example : mergeSortTR₂ [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] (fun x y => x/10 ≤ y/10) = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  by native_decide

/-!
# Behaviour of mergeSort when the comparator is not provided, but typeclasses are missing.
-/

inductive NoLE
| mk : NoLE

/--
error: could not synthesize default value for parameter 'le' using tactics
---
error: failed to synthesize instance of type class
  LE NoLE

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : mergeSort [NoLE.mk] = [NoLE.mk] := sorry

inductive UndecidableLE
| mk : UndecidableLE

instance : LE UndecidableLE where
  le := fun _ _ => true

/--
error: could not synthesize default value for parameter 'le' using tactics
---
error: Type mismatch
  a ≤ b
has type
  Prop
but is expected to have type
  Bool
-/
#guard_msgs in
example : mergeSort [UndecidableLE.mk] = [UndecidableLE.mk] := sorry

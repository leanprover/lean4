open List MergeSort Internal

-- If we omit the comparator, it is filled by the autoparam `fun a b => a ≤ b`
unseal mergeSort merge in
example : mergeSort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSort merge in
example : mergeSort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] (· ≤ ·) = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSort merge in
example : mergeSort [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] (fun x y => x/10 ≤ y/10) = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  rfl

unseal mergeSortTR.run mergeTR.go in
example : mergeSortTR [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSortTR.run mergeTR.go in
example : mergeSortTR [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] (fun x y => x/10 ≤ y/10) = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  rfl

unseal mergeSortTR₂.run mergeTR.go in
example : mergeSortTR₂ [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  rfl

unseal mergeSortTR₂.run mergeTR.go in
example : mergeSortTR₂ [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5] (fun x y => x/10 ≤ y/10) = [3, 4, 5, 2, 5, 5, 16, 13, 101, 101, 109] :=
  rfl

/-!
# Behaviour of mergeSort when the comparator is not provided, but typeclasses are missing.
-/

inductive NoLE
| mk : NoLE

/--
error: could not synthesize default value for parameter 'le' using tactics
---
error: failed to synthesize
  LE NoLE

Additional diagnostic information may be available using the `set_option diagnostics true` command.
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
error: type mismatch
  a ≤ b
has type
  Prop : Type
but is expected to have type
  Bool : Type
-/
#guard_msgs in
example : mergeSort [UndecidableLE.mk] = [UndecidableLE.mk] := sorry

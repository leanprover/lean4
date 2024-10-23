
/-!
Because `Array.isEqvAux` was defined by well-founded recursion, this used to fail with
```
tactic 'decide' failed for proposition
  #[0, 1] = #[0, 1]
since its 'Decidable' instance
  #[0, 1].instDecidableEq #[0, 1]
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqNat', 'Array.instDecidableEq' and 'Nat.decEq', reduction got stuck at the 'Decidable' instance
  match h : #[0, 1].isEqv #[0, 1] fun a b => decide (a = b) with
  | true => isTrue ⋯
  | false => isFalse ⋯
```
-/

example : #[0, 1] = #[0, 1] := by decide

example : let a := Array.range (10^6); a == a := by native_decide

/-!
There are other `Array` functions that use well-founded recursion,
which we've marked as `@[semireducible]`. We test that `decide` can unfold them here.
-/

example : Array.ofFn (id : Fin 2 → Fin 2) = #[0, 1] := by decide

example : #[0, 1].map (· + 1) = #[1, 2] := by decide

example : #[0, 1].any (· % 2 = 0) := by decide

example : #[0, 1].findIdx? (· % 2 = 0) = some 0 := by decide

example : #[0, 1, 2].popWhile (· % 2 = 0) = #[0, 1] := by decide

example : #[0, 1, 2].takeWhile (· % 2 = 0) = #[0] := by decide

example : #[0, 1, 2].feraseIdx ⟨1, by decide⟩ = #[0, 2] := by decide

example : #[0, 1, 2].insertAt ⟨1, by decide⟩ 3 = #[0, 3, 1, 2] := by decide

example : #[0, 1, 2].isPrefixOf #[0, 1, 2, 3] = true := by decide

example : #[0, 1, 2].zipWith #[3, 4, 5] (· + ·) = #[3, 5, 7] := by decide

example : #[0, 1, 2].allDiff = true := by decide

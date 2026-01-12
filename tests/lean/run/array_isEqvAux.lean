
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
There are other `Array` functions that use well-founded recursion.
For a while we marked them as `@[semireducible]`, but this is now dropped.
We can still use `native_decide` of course, and should be able to use `simp`:
-/

example : Array.ofFn (id : Fin 2 → Fin 2) = #[0, 1] := by decide

example : #[0, 1].map (· + 1) = #[1, 2] := by native_decide
example : #[0, 1].map (· + 1) = #[1, 2] := by simp

example : #[0, 1].any (· % 2 = 0) := by native_decide
example : #[0, 1].any (· % 2 = 0) := by simp

example : #[0, 1].findIdx? (· % 2 = 0) = some 0 := by native_decide
example : #[0, 1].findIdx? (· % 2 = 0) = some 0 := by simp [List.findIdx?_cons]

example : #[0, 1, 2].popWhile (· % 2 = 0) = #[0, 1] := by native_decide
example : #[0, 1, 2].popWhile (· % 2 = 0) = #[0, 1] := by simp

example : #[0, 1, 2].takeWhile (· % 2 = 0) = #[0] := by native_decide
example : #[0, 1, 2].takeWhile (· % 2 = 0) = #[0] := by simp

example : #[0, 1, 2].eraseIdx 1 = #[0, 2] := by native_decide
example : #[0, 1, 2].eraseIdx 1 = #[0, 2] := by simp

example : #[0, 1, 2].insertIdx 1 3 = #[0, 3, 1, 2] := by native_decide
example : #[0, 1, 2].insertIdx 1 3 = #[0, 3, 1, 2] := by simp

example : #[0, 1, 2].isPrefixOf #[0, 1, 2, 3] = true := by native_decide
example : #[0, 1, 2].isPrefixOf #[0, 1, 2, 3] = true := by simp

example : Array.zipWith (· + ·) #[0, 1, 2] #[3, 4, 5] = #[3, 5, 7] := by native_decide
example : Array.zipWith (· + ·) #[0, 1, 2] #[3, 4, 5] = #[3, 5, 7] := by simp

example : #[0, 1, 2].allDiff = true := by native_decide
-- no API for allDiff yet:
-- example : #[0, 1, 2].allDiff = true := by simp

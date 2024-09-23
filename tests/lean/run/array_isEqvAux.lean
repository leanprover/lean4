/-!
Because `Array.isEqvAux` was defined by well-founded recursion, this used to fail with
```
tactic 'decide' failed for proposition
  Array.ofFn id = #[0, 1]
since its 'Decidable' instance
  (Array.ofFn id).instDecidableEq #[0, 1]
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'instDecidableEqNat', 'Array.instDecidableEq' and 'Nat.decEq', reduction got stuck at the 'Decidable' instance
  match h : (Array.ofFn id).isEqv #[0, 1] fun a b => decide (a = b) with
  | true => isTrue ⋯
  | false => isFalse ⋯
```
-/

example : Array.ofFn (id : Fin 2 → Fin 2) = #[0, 1] := by decide

/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
prelude
import Init.Data.Nat.Linear

namespace Fin

/-- Folds over `Fin n` from the left: `foldl 3 f x = f (f (f x 0) 1) 2`. -/
@[inline] def foldl (n) (f : α → Fin n → α) (init : α) : α := loop init 0 where
  /-- Inner loop for `Fin.foldl`. `Fin.foldl.loop n f x i = f (f (f x i) ...) (n-1)`  -/
  loop (x : α) (i : Nat) : α :=
    if h : i < n then loop (f x ⟨i, h⟩) (i+1) else x
  termination_by n - i
  decreasing_by decreasing_trivial_pre_omega

/-- Folds over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`. -/
@[inline] def foldr (n) (f : Fin n → α → α) (init : α) : α := loop ⟨n, Nat.le_refl n⟩ init where
  /-- Inner loop for `Fin.foldr`. `Fin.foldr.loop n f i x = f 0 (f ... (f (i-1) x))`  -/
  loop : {i // i ≤ n} → α → α
  | ⟨0, _⟩, x => x
  | ⟨i+1, h⟩, x => loop ⟨i, Nat.le_of_lt h⟩ (f ⟨i, h⟩ x)

end Fin

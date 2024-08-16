/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Pairwise

/-!
# Lemmas about `List.range` and `List.enum`

Most of the results are deferred to `Data.Init.List.Nat.Range`, where more results about
natural arithmetic are available.
-/

namespace List

open Nat

/-! ## Ranges and enumeration -/

/-! ### enumFrom -/

@[simp]
theorem enumFrom_eq_nil {n : Nat} {l : List α} : List.enumFrom n l = [] ↔ l = [] := by
  cases l <;> simp

@[simp] theorem enumFrom_length : ∀ {n} {l : List α}, (enumFrom n l).length = l.length
  | _, [] => rfl
  | _, _ :: _ => congrArg Nat.succ enumFrom_length

@[simp]
theorem getElem?_enumFrom :
    ∀ n (l : List α) m, (enumFrom n l)[m]? = l[m]?.map fun a => (n + m, a)
  | n, [], m => rfl
  | n, a :: l, 0 => by simp
  | n, a :: l, m + 1 => by
    simp only [enumFrom_cons, getElem?_cons_succ]
    exact (getElem?_enumFrom (n + 1) l m).trans <| by rw [Nat.add_right_comm]; rfl

@[simp]
theorem getElem_enumFrom (l : List α) (n) (i : Nat) (h : i < (l.enumFrom n).length) :
    (l.enumFrom n)[i] = (n + i, l[i]'(by simpa [enumFrom_length] using h)) := by
  simp only [enumFrom_length] at h
  rw [getElem_eq_getElem?]
  simp only [getElem?_enumFrom, getElem?_eq_getElem h]
  simp

theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : Nat) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l :=
  ext_getElem? fun i ↦ by simp [(· ∘ ·), Nat.add_comm, Nat.add_left_comm]; rfl

theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : Nat) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _

end List

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Util

@[never_extract]
private def outOfBounds [Inhabited α] : α :=
  panic! "index out of bounds"

/--
The class `GetElem coll idx elem valid` implements the `xs[i]` notation.
Given `xs[i]` with `xs : coll` and `i : idx`, Lean looks for an instance of
`GetElem coll idx elem valid` and uses this to infer the type of return
value `elem` and side conditions `valid` required to ensure `xs[i]` yields
a valid value of type `elem`.

For example, the instance for arrays looks like
`GetElem (Array α) Nat α (fun xs i => i < xs.size)`.

The proof side-condition `valid xs i` is automatically dispatched by the
`get_elem_tactic` tactic, which can be extended by adding more clauses to
`get_elem_tactic_trivial`.
-/
class GetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
              (valid : outParam (coll → idx → Prop)) where
  /--
  The syntax `arr[i]` gets the `i`'th element of the collection `arr`.
  If there are proof side conditions to the application, they will be automatically
  inferred by the `get_elem_tactic` tactic.

  The actual behavior of this class is type-dependent, but here are some
  important implementations:
  * `arr[i] : α` where `arr : Array α` and `i : Nat` or `i : USize`:
    does array indexing with no bounds check and a proof side goal `i < arr.size`.
  * `l[i] : α` where `l : List α` and `i : Nat`: index into a list,
    with proof side goal `i < l.length`.
  * `stx[i] : Syntax` where `stx : Syntax` and `i : Nat`: get a syntax argument,
    no side goal (returns `.missing` out of range)

  There are other variations on this syntax:
  * `arr[i]`: proves the proof side goal by `get_elem_tactic`
  * `arr[i]!`: panics if the side goal is false
  * `arr[i]?`: returns `none` if the side goal is false
  * `arr[i]'h`: uses `h` to prove the side goal
  -/
  getElem (xs : coll) (i : idx) (h : valid xs i) : elem

  getElem? (xs : coll) (i : idx) [Decidable (valid xs i)] : Option elem :=
    if h : _ then some (getElem xs i h) else none

  getElem! [Inhabited elem] (xs : coll) (i : idx) [Decidable (valid xs i)] : elem :=
    match getElem? xs i with | some e => e | none => outOfBounds

export GetElem (getElem getElem! getElem?)

@[inherit_doc getElem]
syntax:max term noWs "[" withoutPosition(term) "]" : term
macro_rules | `($x[$i]) => `(getElem $x $i (by get_elem_tactic))

@[inherit_doc getElem]
syntax term noWs "[" withoutPosition(term) "]'" term:max : term
macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

/--
The syntax `arr[i]?` gets the `i`'th element of the collection `arr` or
returns `none` if `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)

/--
The syntax `arr[i]!` gets the `i`'th element of the collection `arr` and
panics `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)

class LawfulGetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w))
   (dom : outParam (cont → idx → Prop)) [ge : GetElem cont idx elem dom] : Prop where

  getElem?_def (c : cont) (i : idx) [Decidable (dom c i)] :
    c[i]? = if h : dom c i then some (c[i]'h) else none := by intros; eq_refl
  getElem!_def [Inhabited elem] (c : cont) (i : idx) [Decidable (dom c i)] :
    c[i]! = match c[i]? with | some e => e | none => default := by intros; eq_refl

export LawfulGetElem (getElem?_def getElem!_def)

theorem getElem?_pos [GetElem cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) [Decidable (dom c i)] : c[i]? = some (c[i]'h) := by
  rw [getElem?_def]
  exact dif_pos h

theorem getElem?_neg [GetElem cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : ¬dom c i) [Decidable (dom c i)] : c[i]? = none := by
  rw [getElem?_def]
  exact dif_neg h

theorem getElem!_pos [GetElem cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : dom c i) [Decidable (dom c i)] :
    c[i]! = c[i]'h := by
  simp only [getElem!_def, getElem?_def, h]

theorem getElem!_neg [GetElem cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : ¬dom c i) [Decidable (dom c i)] : c[i]! = default := by
  simp only [getElem!_def, getElem?_def, h]

namespace Fin

instance instGetElemFinVal [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
  getElem xs i h := getElem xs i.1 h
  getElem? xs i := getElem? xs i.val
  getElem! xs i := getElem! xs i.val

instance [GetElem cont Nat elem dom] [h : LawfulGetElem cont Nat elem dom] :
      LawfulGetElem cont (Fin n) elem fun xs i => dom xs i where

  getElem?_def _c _i _d := h.getElem?_def ..
  getElem!_def _c _i _d := h.getElem!_def ..

@[simp] theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

@[simp] theorem getElem?_fin [h : GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] : a[i]? = a[i.1]? := by rfl

@[simp] theorem getElem!_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] [Inhabited Elem] : a[i]! = a[i.1]! := rfl

macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)

end Fin

namespace List

instance : GetElem (List α) Nat α fun as i => i < as.length where
  getElem as i h := as.get ⟨i, h⟩

instance : LawfulGetElem (List α) Nat α fun as i => i < as.length where

@[simp] theorem cons_getElem_zero (a : α) (as : List α) (h : 0 < (a :: as).length) : getElem (a :: as) 0 h = a := by
  rfl

@[simp] theorem cons_getElem_succ (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) := by
  rfl

theorem get_drop_eq_drop (as : List α) (i : Nat) (h : i < as.length) : as[i] :: as.drop (i+1) = as.drop i :=
  match as, i with
  | _::_, 0   => rfl
  | _::_, i+1 => get_drop_eq_drop _ i _

end List

namespace Array

instance : GetElem (Array α) Nat α fun xs i => i < xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

instance : LawfulGetElem (Array α) Nat α fun xs i => i < xs.size where

end Array

namespace Lean.Syntax

instance : GetElem Syntax Nat Syntax fun _ _ => True where
  getElem stx i _ := stx.getArg i

instance : LawfulGetElem Syntax Nat Syntax fun _ _ => True where

end Lean.Syntax

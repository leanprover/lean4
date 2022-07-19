/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Except
import Init.Data.ByteArray
import Init.SimpLemmas
import Init.Data.Nat.Linear
import Init.Util
import Init.WFTactics

namespace String

def toNat! (s : String) : Nat :=
  if s.isNat then
    s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    panic! "Nat expected"

/--
  Convert a UTF-8 encoded `ByteArray` string to `String`.
  The result is unspecified if `a` is not properly UTF-8 encoded. -/
@[extern "lean_string_from_utf8_unchecked"]
opaque fromUTF8Unchecked (a : @& ByteArray) : String

@[extern "lean_string_to_utf8"]
opaque toUTF8 (a : @& String) : ByteArray

theorem one_le_csize (c : Char) : 1 ≤ csize c := by
  simp [csize, Char.utf8Size]
  repeat (first | split | decide)

@[simp] theorem pos_lt_eq (p₁ p₂ : Pos) : (p₁ < p₂) = (p₁.1 < p₂.1) := rfl

@[simp] theorem pos_add_char (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + csize c := rfl

theorem eq_empty_of_bsize_eq_zero (h : s.endPos = {}) : s = "" := by
  match s with
  | ⟨[]⟩   => rfl
  | ⟨c::cs⟩ =>
    injection h with h
    simp [endPos, utf8ByteSize, utf8ByteSize.go] at h
    have : utf8ByteSize.go cs + 1 ≤ utf8ByteSize.go cs + csize c := Nat.add_le_add_left (one_le_csize c) _
    simp_arith [h] at this

theorem lt_next (s : String) (i : String.Pos) : i.1 < (s.next i).1 := by
  simp_arith [next]; apply one_le_csize

theorem Iterator.sizeOf_next_lt_of_hasNext (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  have := String.lt_next s pos
  apply Nat.sub.elim (motive := fun k => k < _) (utf8ByteSize s) (String.next s pos).1
  . intro _ k he
    simp [he]; rw [Nat.add_comm, Nat.add_sub_assoc (Nat.le_of_lt this)]
    have := Nat.zero_lt_sub_of_lt this
    simp_all_arith
  . intro; apply Nat.zero_lt_sub_of_lt h

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply String.Iterator.sizeOf_next_lt_of_hasNext; assumption)

theorem Iterator.sizeOf_next_lt_of_atEnd (i : String.Iterator) (h : ¬ i.atEnd = true) : sizeOf i.next < sizeOf i :=
  have h : i.hasNext = true := by simp_arith [atEnd] at h; simp_arith [hasNext, h]
  sizeOf_next_lt_of_hasNext i h

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply String.Iterator.sizeOf_next_lt_of_atEnd; assumption)

namespace Iterator

@[specialize] def find (it : Iterator) (p : Char → Bool) : Iterator :=
  if it.atEnd then it
  else if p it.curr then it
  else find it.next p

@[specialize] def foldUntil (it : Iterator) (init : α) (f : α → Char → Option α) : α × Iterator :=
  if it.atEnd then 
    (init, it)
  else if let some a := f init it.curr then 
    foldUntil it.next a f
  else
    (init, it)

end Iterator

end String

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
constant fromUTF8Unchecked (a : @& ByteArray) : String

@[extern "lean_string_to_utf8"]
constant toUTF8 (a : @& String) : ByteArray

theorem one_le_csize (c : Char) : 1 ≤ csize c := by
  simp [csize, Char.utf8Size]
  repeat (first | split | decide)

theorem eq_empty_of_bsize_eq_zero (h : s.bsize = 0) : s = "" := by
  match s with
  | ⟨[]⟩   => rfl
  | ⟨c::cs⟩ =>
    simp [bsize, utf8ByteSize, utf8ByteSize.go] at h
    have : utf8ByteSize.go cs + 1 ≤ utf8ByteSize.go cs + csize c := Nat.add_le_add_left (one_le_csize c) _
    simp_arith [h] at this

theorem lt_next (s : String) (i : String.Pos) : i < s.next i := by
  simp_arith [next]; apply one_le_csize

theorem Iterator.sizeOf_next_lt (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  have := String.lt_next s pos
  apply Nat.sub.elim (motive := fun k => k < _) (utf8ByteSize s) (String.next s pos)
  . intro hle k he
    simp [he]; rw [Nat.add_comm, Nat.add_sub_assoc (Nat.le_of_lt this)]
    have := Nat.zero_lt_sub_of_lt this
    simp_all_arith
  . intro; apply Nat.zero_lt_sub_of_lt h

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply String.Iterator.sizeOf_next_lt; assumption)

end String

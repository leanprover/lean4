/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.data.char.basic

private structure string_imp :=
(data : list char)

def string := string_imp

def list.as_string (s : list char) : string :=
⟨s.reverse⟩

namespace string
def empty : string :=
⟨list.nil⟩

instance : inhabited string :=
⟨empty⟩

def length : string → nat
| ⟨s⟩  := s.length

instance : has_sizeof string :=
⟨string.length⟩

def str : string → char → string
| ⟨s⟩ c := ⟨c::s⟩

def append : string → string → string
| ⟨a⟩ ⟨b⟩ := ⟨b ++ a⟩

def is_empty : string → bool
| ⟨[]⟩ := tt
| _    := ff

instance : has_append string :=
⟨string.append⟩

def to_list : string → list char
| ⟨s⟩ := s.reverse

def pop_back : string → string
| ⟨s⟩ := ⟨s.tail⟩

def popn_back : string → nat → string
| ⟨s⟩ n := ⟨s.drop n⟩

def intercalate (s : string) (ss : list string) : string :=
(list.intercalate s.to_list (ss.map to_list)).as_string

def fold {α} (a : α) (f : α → char → α) (s : string) : α :=
s.to_list.foldl f a

def front (s : string) : char :=
s.to_list.head

def back : string → char
| ⟨[]⟩    := default char
| ⟨c::cs⟩ := c

def backn : string → nat → string
| ⟨s⟩ n := ⟨s.take n⟩

def join (l : list string) : string :=
l.foldl (λ r s, r ++ s) ""

def singleton (c : char) : string :=
str empty c

end string

open list string

private def utf8_length_aux : nat → nat → list char → nat
| 0 r (c::s) :=
  let n := char.to_nat c in
  if                 n < 0x80 then utf8_length_aux 0 (r+1) s
  else if 0xC0 ≤ n ∧ n < 0xE0 then utf8_length_aux 1 (r+1) s
  else if 0xE0 ≤ n ∧ n < 0xF0 then utf8_length_aux 2 (r+1) s
  else if 0xF0 ≤ n ∧ n < 0xF8 then utf8_length_aux 3 (r+1) s
  else if 0xF8 ≤ n ∧ n < 0xFC then utf8_length_aux 4 (r+1) s
  else if 0xFC ≤ n ∧ n < 0xFE then utf8_length_aux 5 (r+1) s
  else                             utf8_length_aux 0 (r+1) s
| (n+1) r (c::s) := utf8_length_aux n r s
| n     r []     := r

def string.utf8_length : string → nat
| s := utf8_length_aux 0 0 s.to_list

export string (utf8_length)

private def to_nat_core : list char → nat → nat
| []      r := r
| (c::cs) r :=
  to_nat_core cs (char.to_nat c - char.to_nat '0' + r*10)

def string.to_nat (s : string) : nat :=
to_nat_core s.to_list 0

protected def char.to_string (c : char) : string :=
string.str "" c

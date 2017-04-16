/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.data.char.basic

def string := list char

namespace string
@[pattern] def empty : string := list.nil

instance : inhabited string :=
⟨empty⟩

instance : has_sizeof string :=
⟨list.sizeof⟩

@[pattern] def str : char → string → string := list.cons

def concat (a b : string) : string :=
list.append b a

instance : has_append string :=
⟨string.concat⟩
end string

open list

private def utf8_length_aux : nat → nat → string → nat
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

def utf8_length : string → nat
| s := utf8_length_aux 0 0 (reverse s)

private def to_nat_core : list char → nat → nat
| []      r := r
| (c::cs) r :=
  to_nat_core cs (char.to_nat c - char.to_nat #"0" + r*10)

def string.to_nat (s : string) : nat :=
to_nat_core s.reverse 0

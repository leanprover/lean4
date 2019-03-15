/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.data.char.basic
import init.data.option.basic

/- In the VM, strings are implemented using a dynamic array and UTF-8 encoding.
   TODO: mark as opaque -/
structure string :=
(data : list char)

attribute [extern cpp "lean::string_mk"] string.mk
attribute [extern cpp "lean::string_data"] string.data

@[extern cpp "lean::string_dec_eq"]
def string.dec_eq (s₁ s₂ : @& string) : decidable (s₁ = s₂) :=
match s₁, s₂ with
| ⟨s₁⟩, ⟨s₂⟩ :=
 if h : s₁ = s₂ then is_true (congr_arg _ h)
 else is_false (λ h', string.no_confusion h' (λ h', absurd h' h))

instance : decidable_eq string :=
{dec_eq := string.dec_eq}

def list.as_string (s : list char) : string :=
⟨s⟩

namespace string
instance : has_lt string :=
⟨λ s₁ s₂, s₁.data < s₂.data⟩

/- Remark: this function has a VM builtin efficient implementation. -/
@[extern cpp "lean::string_dec_lt"]
instance dec_lt (s₁ s₂ : @& string) : decidable (s₁ < s₂) :=
list.has_decidable_lt s₁.data s₂.data

@[extern cpp "lean::string_length"]
def length : (@& string) → nat
| ⟨s⟩  := s.length

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
@[extern cpp "lean::string_push"]
def push : string → char → string
| ⟨s⟩ c := ⟨s ++ [c]⟩

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
@[extern cpp "lean::string_append"]
def append : string → (@& string) → string
| ⟨a⟩ ⟨b⟩ := ⟨a ++ b⟩

/- O(n) in the runtime, where n is the length of the string -/
def to_list (s : string) : list char :=
s.data

private def csize (c : char) : usize :=
usize.of_uint32 c.utf8_size

private def utf8_byte_size_aux : list char → usize → usize
| []      r := r
| (c::cs) r := utf8_byte_size_aux cs (r + csize c)

@[extern cpp "lean::string_utf8_byte_size"]
def utf8_byte_size : (@& string) → usize
| ⟨s⟩ := utf8_byte_size_aux s 0

@[inline] def bsize (s : string) : usize :=
utf8_byte_size s

abbrev utf8_pos := usize

def utf8_begin : utf8_pos := 0

private def utf8_get_aux : list char → usize → usize → char
| []      i p := default char
| (c::cs) i p := if i = p then c else utf8_get_aux cs (i + csize c) p

@[extern cpp "lean::string_utf8_get"]
def utf8_get : (@& string) → utf8_pos → char
| ⟨s⟩ p := utf8_get_aux s 0 p

private def utf8_set_aux (c' : char) : list char → usize → usize → list char
| []      i p := []
| (c::cs) i p :=
  if i = p then (c'::cs) else c::(utf8_set_aux cs (i + csize c) p)

@[extern cpp "lean::string_utf8_set"]
def utf8_set : string → utf8_pos → char → string
| ⟨s⟩ i c := ⟨utf8_set_aux c s 0 i⟩

@[extern cpp "lean::string_utf8_next"]
def utf8_next (s : @& string) (p : utf8_pos) : utf8_pos :=
let c := utf8_get s p in
p + csize c

private def utf8_prev_aux : list char → usize → usize → usize
| []      i p := 0
| (c::cs) i p :=
  let cz := csize c in
  let i' := i + cz in
  if i' = p then i else utf8_prev_aux cs i' p

@[extern cpp "lean::string_utf8_prev"]
def utf8_prev : (@& string) → utf8_pos → utf8_pos
| ⟨s⟩ p := if p = 0 then 0 else utf8_prev_aux s 0 p

def front (s : string) : char :=
utf8_get s 0

def back (s : string) : char :=
utf8_get s (utf8_prev s (bsize s))

@[extern cpp "lean::string_utf8_at_end"]
def utf8_at_end : (@& string) → utf8_pos → bool
| s p := p ≥ utf8_byte_size s

private def utf8_extract_aux₂ : list char → usize → usize → list char
| []      _ _ := []
| (c::cs) i e := if i = e then [] else c :: utf8_extract_aux₂ cs (i + csize c) e

private def utf8_extract_aux₁ : list char → usize → usize → usize → list char
| []        _ _ _ := []
| s@(c::cs) i b e := if i = b then utf8_extract_aux₂ s i e else utf8_extract_aux₁ cs (i + csize c) b e

@[extern cpp "lean::string_utf8_extract"]
def extract : (@& string) → utf8_pos → utf8_pos → string
| ⟨s⟩ b e := if b ≥ e then ⟨[]⟩ else ⟨utf8_extract_aux₁ s 0 b e⟩

def trim_left_aux (s : string) : nat → utf8_pos → utf8_pos
| 0     i := i
| (n+1) i :=
  if i ≥ s.bsize then i
  else let c := s.utf8_get i in
       if !c.is_whitespace then i
       else trim_left_aux n (i + csize c)

def trim_left (s : string) : string :=
let b := trim_left_aux s s.bsize.to_nat 0 in
if b = 0 then s
else s.extract b s.bsize

def trim_right_aux (s : string) : nat → utf8_pos → utf8_pos
| 0     i := i
| (n+1) i :=
  if i = 0 then i
  else
    let i' := s.utf8_prev i in
    let c  := s.utf8_get i' in
    if !c.is_whitespace then i
    else trim_right_aux n i'

def trim_right (s : string) : string :=
let e := trim_right_aux s s.bsize.to_nat s.bsize in
if e = s.bsize then s
else s.extract 0 e

def trim (s : string) : string :=
let b := trim_left_aux s s.bsize.to_nat 0 in
let e := trim_right_aux s s.bsize.to_nat s.bsize in
if b = 0 && e = s.bsize then s
else s.extract b e

structure iterator :=
(s : string) (offset : nat) (i : usize)

def mk_iterator (s : string) : iterator :=
⟨s, 0, 0⟩

namespace iterator
def remaining : iterator → nat
| ⟨s, o, _⟩ := s.length - o

def to_string : iterator → string
| ⟨s, _, _⟩ := s

def remaining_bytes : iterator → usize
| ⟨s, _, i⟩ := s.bsize - i

def curr : iterator → char
| ⟨s, _, i⟩ := utf8_get s i

def next : iterator → iterator
| ⟨s, o, i⟩ := ⟨s, o+1, utf8_next s i⟩

def prev : iterator → iterator
| ⟨s, o, i⟩ := ⟨s, o-1, utf8_prev s i⟩

def has_next : iterator → bool
| ⟨s, _, i⟩ := i < utf8_byte_size s

def has_prev : iterator → bool
| ⟨s, _, i⟩ := i > 0

def set_curr : iterator → char → iterator
| ⟨s, o, i⟩ c := ⟨utf8_set s i c, o, i⟩

def to_end : iterator → iterator
| ⟨s, o, _⟩ := ⟨s, s.length, s.bsize⟩

def extract : iterator → iterator → string
| ⟨s₁, _, b⟩ ⟨s₂, _, e⟩ :=
  if s₁ ≠ s₂ || b > e then ""
  else s₁.extract b e

def forward : iterator → nat → iterator
| it 0     := it
| it (n+1) := forward it.next n

def remaining_to_string : iterator → string
| ⟨s, _, i⟩ := s.extract i s.bsize

/- (is_prefix_of_remaining it₁ it₂) is `tt` iff `it₁.remaining_to_string` is a prefix
   of `it₂.remaining_to_string`. -/
def is_prefix_of_remaining : iterator → iterator → bool
| ⟨s₁, _, i₁⟩ ⟨s₂, _, i₂⟩ := s₁.extract i₁ s₁.bsize = s₂.extract i₂ (i₂ + (s₁.bsize - i₁))

end iterator
end string

/- The following definitions do not have builtin support in the VM -/

instance : inhabited string :=
⟨""⟩

instance : has_sizeof string :=
⟨string.length⟩

instance : has_append string :=
⟨string.append⟩

namespace string
def str : string → char → string := push

def pushn (s : string) (c : char) (n : nat) : string :=
n.repeat (λ _ s, s.push c) s

def is_empty (s : string) : bool :=
to_bool (s.length = 0)

def join (l : list string) : string :=
l.foldl (λ r s, r ++ s) ""

def singleton (c : char) : string :=
"".push c

def intercalate (s : string) (ss : list string) : string :=
(list.intercalate s.to_list (ss.map to_list)).as_string

namespace iterator
def nextn : iterator → nat → iterator
| it 0     := it
| it (i+1) := nextn it.next i

def prevn : iterator → nat → iterator
| it 0     := it
| it (i+1) := prevn it.prev i
end iterator

private def line_column_aux : nat → string.iterator → nat × nat → nat × nat
| 0     it r           := r
| (k+1) it r@(line, col) :=
  if it.has_next = ff then r
  else match it.curr with
       | '\n'  := line_column_aux k it.next (line+1, 0)
       | other := line_column_aux k it.next (line, col+1)

def line_column (s : string) (offset : nat) : nat × nat :=
line_column_aux offset s.mk_iterator (1, 0)
end string

protected def char.to_string (c : char) : string :=
string.singleton c

private def to_nat_core : string.iterator → nat → nat → nat
| it      0     r := r
| it      (i+1) r :=
  let c := it.curr in
  let r := r*10 + c.to_nat - '0'.to_nat in
  to_nat_core it.next i r

def string.to_nat (s : string) : nat :=
to_nat_core s.mk_iterator s.length 0

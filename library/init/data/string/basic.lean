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

instance string.dec_eq : decidable_eq string :=
{dec_eq := λ ⟨s₁⟩ ⟨s₂⟩,
 if h : s₁ = s₂ then is_true (congr_arg _ h)
 else is_false (λ h', string.no_confusion h' (λ h', absurd h' h))}

def list.as_string (s : list char) : string :=
⟨s⟩

namespace string
instance : has_lt string :=
⟨λ s₁ s₂, s₁.data < s₂.data⟩

/- Remark: this function has a VM builtin efficient implementation. -/
instance dec_lt (s₁ s₂ : string) : decidable (s₁ < s₂) :=
list.has_decidable_lt s₁.data s₂.data

def empty : string :=
⟨[]⟩

def length : string → nat
| ⟨s⟩  := s.length

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
def push : string → char → string
| ⟨s⟩ c := ⟨s ++ [c]⟩

/- The internal implementation uses dynamic arrays and will perform destructive updates
   if the string is not shared. -/
def append : string → string → string
| ⟨a⟩ ⟨b⟩ := ⟨a ++ b⟩

/- O(n) in the VM, where n is the length of the string -/
def to_list (s : string) : list char :=
s.data

/- In the VM, the string iterator is implemented as a pointer to the string being iterated + index.
   TODO: mark it opaque. -/
structure iterator :=
(fst : list char) (snd : list char)

def mk_iterator : string → iterator
| ⟨s⟩ := ⟨[], s⟩

namespace iterator
def remaining : iterator → nat
| ⟨p, n⟩ := n.length

def offset : iterator → nat
| ⟨p, n⟩ := p.length

def curr : iterator → char
| ⟨p, c::n⟩ := c
| _         := default char

/- In the VM, `set_curr` is constant time if the string being iterated is not shared and linear time
   if it is. -/
def set_curr : iterator → char → iterator
| ⟨p, c::n⟩ c' := ⟨p, c'::n⟩
| it        c' := it

def next : iterator → iterator
| ⟨p, c::n⟩ := ⟨c::p, n⟩
| ⟨p, []⟩   := ⟨p, []⟩

def prev : iterator → iterator
| ⟨c::p, n⟩ := ⟨p, c::n⟩
| ⟨[],   n⟩ := ⟨[], n⟩

def has_next : iterator → bool
| ⟨p, []⟩ := ff
| _       := tt

def has_prev : iterator → bool
| ⟨[], n⟩ := ff
| _       := tt

def insert : iterator → string → iterator
| ⟨p, n⟩ ⟨s⟩ := ⟨p, s++n⟩

def remove : iterator → nat → iterator
| ⟨p, n⟩ m := ⟨p, n.drop m⟩

/- In the VM, `to_string` is a constant time operation. -/
def to_string : iterator → string
| ⟨p, n⟩ := ⟨p.reverse ++ n⟩

def forward : iterator → nat → iterator
| it 0     := it
| it (n+1) := forward it.next n

def to_end : iterator → iterator
| ⟨p, n⟩ := ⟨n.reverse ++ p, []⟩

def remaining_to_string : iterator → string
| ⟨p, n⟩ := ⟨n⟩

def prev_to_string : iterator → string
| ⟨p, n⟩ := ⟨p.reverse⟩

protected def extract_core : list char → list char → option (list char)
| []       cs  := none
| (c::cs₁) cs₂ :=
  if cs₁ = cs₂ then some [c] else
  match extract_core cs₁ cs₂ with
  | none   := none
  | some r := some (c::r)

def extract : iterator → iterator → option string
| ⟨p₁, n₁⟩ ⟨p₂, n₂⟩ :=
  if p₁.reverse ++ n₁ ≠ p₂.reverse ++ n₂ then none
  else if n₁ = n₂ then some ""
  else (match iterator.extract_core n₁ n₂ with
        | none := none
        | some r := some ⟨r⟩)

/- (is_prefix_of_remaining it₁ it₂) is true iff `it₁.remaining_to_string` is a prefix
   of `it₂.remaining_to_string`. -/
def is_prefix_of_remaining (it₁ it₂ : iterator) : Prop :=
it₂.extract (it₂.forward it₁.remaining) = some it₁.remaining_to_string

instance : decidable_rel is_prefix_of_remaining :=
λ it₁ it₂, infer_instance_as $ decidable $
  it₂.extract (it₂.forward it₁.remaining) = some it₁.remaining_to_string

end iterator
end string

/- The following definitions do not have builtin support in the VM -/

instance : inhabited string :=
⟨string.empty⟩

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

def front (s : string) : char :=
s.mk_iterator.curr

def back (s : string) : char :=
s.mk_iterator.to_end.prev.curr

def join (l : list string) : string :=
l.foldl (λ r s, r ++ s) ""

def singleton (c : char) : string :=
empty.push c

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

def pop_back (s : string) : string :=
s.mk_iterator.to_end.prev.prev_to_string

def popn_back (s : string) (n : nat) : string :=
(s.mk_iterator.to_end.prevn n).prev_to_string

def backn (s : string) (n : nat) : string :=
(s.mk_iterator.to_end.prevn n).remaining_to_string

private def trim_left_aux : nat → iterator → iterator
| 0 it := it
| (n+1) it :=
  if it.curr.is_whitespace then trim_left_aux n it.next
  else it

def trim_left (s : string) : string :=
(trim_left_aux s.length s.mk_iterator).remaining_to_string

private def trim_right_aux : nat → iterator → iterator
| 0 it := it
| (n+1) it :=
  let it' := it.prev in
  if it'.curr.is_whitespace then trim_right_aux n it'
  else it

def trim_right (s : string) : string :=
(trim_right_aux s.length s.mk_iterator.to_end).prev_to_string

def trim (s : string) : string :=
let l := trim_left_aux s.length s.mk_iterator in
let r := trim_right_aux s.length s.mk_iterator.to_end in
(l.extract r).get_or_else ""

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

namespace string

private lemma nil_ne_append_singleton : ∀ (c : char) (l : list char), [] ≠ l ++ [c]
| c []     := λ h, list.no_confusion h
| c (d::l) := λ h, list.no_confusion h

lemma empty_ne_str : ∀ (c : char) (s : string), empty ≠ str s c
| c ⟨l⟩ :=
  λ h : string.mk [] = string.mk (l ++ [c]),
    string.no_confusion h $ λ h, nil_ne_append_singleton _ _ h

lemma str_ne_empty (c : char) (s : string) : str s c ≠ empty :=
(empty_ne_str c s).symm

private lemma str_ne_str_left_aux : ∀ {c₁ c₂ : char} (l₁ l₂ : list char), c₁ ≠ c₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
| c₁ c₂ []       [] h₁ h₂ := list.no_confusion h₂ (λ h _, absurd h h₁)
| c₁ c₂ (d₁::l₁) [] h₁ h₂ :=
  have d₁ :: (l₁ ++ [c₁]) = [c₂], from h₂,
  have l₁ ++ [c₁] = [], from list.no_confusion this (λ _ h, h),
  absurd this.symm (nil_ne_append_singleton _ _)
| c₁ c₂ [] (d₂::l₂) h₁ h₂ :=
  have [c₁] = d₂ :: (l₂ ++ [c₂]), from h₂,
  have []   = l₂ ++ [c₂], from list.no_confusion this (λ _ h, h),
  absurd this (nil_ne_append_singleton _ _)
| c₁ c₂ (d₁::l₁) (d₂::l₂) h₁ h₂ :=
  have d₁ :: (l₁ ++ [c₁]) = d₂ :: (l₂ ++ [c₂]), from h₂,
  have l₁ ++ [c₁] = l₂ ++ [c₂], from list.no_confusion this (λ _ h, h),
  absurd this (str_ne_str_left_aux l₁ l₂ h₁)

lemma str_ne_str_left : ∀ {c₁ c₂ : char} (s₁ s₂ : string), c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂
| c₁ c₂ (string.mk l₁) (string.mk l₂) h₁ h₂ :=
  have l₁ ++ [c₁] = l₂ ++ [c₂], from string.no_confusion h₂ id,
  absurd this (str_ne_str_left_aux l₁ l₂ h₁)

private lemma str_ne_str_right_aux : ∀ (c₁ c₂ : char) {l₁ l₂ : list char}, l₁ ≠ l₂ → l₁ ++ [c₁] ≠ l₂ ++ [c₂]
| c₁ c₂ []       [] h₁ h₂ := absurd rfl h₁
| c₁ c₂ (d₁::l₁) [] h₁ h₂ :=
  have d₁ :: (l₁ ++ [c₁]) = [c₂], from h₂,
  have l₁ ++ [c₁] = [], from list.no_confusion this (λ _ h, h),
  absurd this.symm (nil_ne_append_singleton _ _)
| c₁ c₂ [] (d₂::l₂) h₁ h₂ :=
  have [c₁] = d₂ :: (l₂ ++ [c₂]), from h₂,
  have []   = l₂ ++ [c₂], from list.no_confusion this (λ _ h, h),
  absurd this (nil_ne_append_singleton _ _)
| c₁ c₂ (d₁::l₁) (d₂::l₂) h₁ h₂ :=
  have aux₁ : d₁ :: (l₁ ++ [c₁]) = d₂ :: (l₂ ++ [c₂]), from h₂,
  have d₁ = d₂, from list.no_confusion aux₁ (λ h _, h),
  have aux₂ : l₁ ≠ l₂, from λ h,
    have d₁ :: l₁ = d₂ :: l₂, from eq.subst h (eq.subst this rfl),
    absurd this h₁,
  have l₁ ++ [c₁] = l₂ ++ [c₂], from list.no_confusion aux₁ (λ _ h, h),
  absurd this (str_ne_str_right_aux c₁ c₂ aux₂)

lemma str_ne_str_right : ∀ (c₁ c₂ : char) {s₁ s₂ : string}, s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂
| c₁ c₂ (string.mk l₁) (string.mk l₂) h₁ h₂ :=
  have aux : l₁ ≠ l₂, from λ h,
    have string.mk l₁ = string.mk l₂, from eq.subst h rfl,
    absurd this h₁,
  have l₁ ++ [c₁] = l₂ ++ [c₂], from string.no_confusion h₂ id,
  absurd this (str_ne_str_right_aux c₁ c₂ aux)

end string

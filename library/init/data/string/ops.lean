/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.data.bool.lemmas
import init.data.string.basic
import init.meta.well_founded_tactics

namespace string

namespace iterator

@[simp] lemma next_to_string_mk_iterator (s : string) : s.mk_iterator.next_to_string = s :=
by induction s; refl

@[simp] lemma length_next_to_string_next (it : iterator) :
  it.next.next_to_string.length = it.next_to_string.length - 1 :=
by cases it; cases it_snd; simp [iterator.next, iterator.next_to_string, string.length, nat.add_sub_cancel_left]

lemma zero_lt_length_next_to_string_of_has_next {it : iterator} :
  it.has_next → 0 < it.next_to_string.length :=
by cases it; cases it_snd; simp [iterator.has_next, iterator.next_to_string, string.length, nat.zero_lt_one_add]

end iterator

-- TODO(Sebastian): generalize to something like https://doc.rust-lang.org/std/primitive.str.html#method.split
private def split_core (p : char → bool) : iterator → iterator → list string
| start stop :=
if h : stop.has_next then
  -- wf hint
  have stop.next_to_string.length - 1 < stop.next_to_string.length,
    from nat.sub_lt (iterator.zero_lt_length_next_to_string_of_has_next h) dec_trivial,
  if p stop.curr then
    let rest := stop.next.next_to_string in
    (start.extract stop).get_or_else "" :: split_core stop.next stop.next
  else
    split_core start stop.next
else
  [start.next_to_string]
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ e, e.2.next_to_string.length)⟩] }

def split (p : char → bool) (s : string) : list string :=
split_core p s.mk_iterator s.mk_iterator

end string

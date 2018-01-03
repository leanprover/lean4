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
-- TODO(Sebastian): run-time quadratic in the number of occurrences because of string copies
private def split_core (p : char → bool) : iterator → list string
| it :=
if h : it.has_next then
  -- wf hint
  have it.next_to_string.length - 1 < it.next_to_string.length,
    from nat.sub_lt (iterator.zero_lt_length_next_to_string_of_has_next h) dec_trivial,
  if p it.curr then
    let rest := it.next.next_to_string in
    it.prev_to_string :: split_core rest.mk_iterator
  else
    split_core it.next
else
  [it.to_string]
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ it, it.next_to_string.length)⟩] }

def split (p : char → bool) (s : string) : list string :=
split_core p s.mk_iterator

end string

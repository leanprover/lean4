/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.data.repr init.meta.format
import init.meta.contradiction_tactic init.meta.constructor_tactic
import init.meta.relation_tactics init.meta.injection_tactic

/--  We can specify the scope of application of some tactics using
   the following type.

   - all : all occurrences of a given term are considered.

   - pos [1, 3] : only the first and third occurrences of a given
     term are consiered.

   - neg [2] : all but the second occurrence of a given term
     are considered. -/
inductive occurrences
| all
| pos : list nat → occurrences
| neg : list nat → occurrences

open occurrences

def occurrences.contains : occurrences → nat → bool
| all                  p := tt
| (occurrences.pos ps) p := p ∈ ps
| (occurrences.neg ps) p := p ∉ ps

instance : inhabited occurrences :=
⟨all⟩

def occurrences_repr : occurrences → string
| occurrences.all     := "*"
| (occurrences.pos l) := repr l
| (occurrences.neg l) := "-" ++ repr l

instance : has_repr occurrences :=
⟨occurrences_repr⟩

meta def occurrences_to_format : occurrences → format
| occurrences.all     := to_fmt "*"
| (occurrences.pos l) := to_fmt l
| (occurrences.neg l) := to_fmt "-" ++ to_fmt l

meta instance : has_to_format occurrences :=
⟨occurrences_to_format⟩

open decidable tactic

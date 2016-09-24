/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.to_string init.meta.format
import init.meta.contradiction_tactic init.meta.constructor_tactic
import init.meta.relation_tactics init.meta.injection_tactic

/-  We can specify the scope of application of some tactics using
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

attribute [instance]
definition occurrences_is_inhabited : inhabited occurrences :=
inhabited.mk all

definition occurrences_to_string : occurrences → string
| occurrences.all     := "*"
| (occurrences.pos l) := to_string l
| (occurrences.neg l) := "-" ++ to_string l

attribute [instance]
definition occurrences_has_to_string : has_to_string occurrences :=
has_to_string.mk occurrences_to_string

meta definition occurrences_to_format : occurrences → format
| occurrences.all     := to_fmt "*"
| (occurrences.pos l) := to_fmt l
| (occurrences.neg l) := to_fmt "-" ++ to_fmt l

attribute [instance]
meta definition occurrences_has_to_format : has_to_format occurrences :=
has_to_format.mk occurrences_to_format

open decidable tactic

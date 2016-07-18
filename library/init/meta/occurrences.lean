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
inductive occurrences :=
| all
| pos : list nat → occurrences
| neg : list nat → occurrences

open occurrences

definition occurrences_is_inhabited [instance] : inhabited occurrences :=
inhabited.mk all

definition occurrences_to_string : occurrences → string
| all     := "*"
| (pos l) := to_string l
| (neg l) := "-" ++ to_string l

definition occurrences_has_to_string [instance] : has_to_string occurrences :=
has_to_string.mk occurrences_to_string

meta_definition occurrences_to_format : occurrences → format
| all     := to_fmt "*"
| (pos l) := to_fmt l
| (neg l) := to_fmt "-" ++ to_fmt l

meta_definition occurrences_has_to_format [instance] : has_to_format occurrences :=
has_to_format.mk occurrences_to_format

open decidable tactic

definition occurrences_has_decidable_eq [instance] : ∀ a b : occurrences, decidable (a = b)
| all      all      := tt rfl
| all      (pos l)  := by left >> intron 1 >> contradiction
| all      (neg l)  := by left >> intron 1 >> contradiction
| (pos l)  all      := by left >> intron 1 >> contradiction
| (pos l₁) (pos l₂) := if H : l₁ = l₂
                       then by right >> get_local "H" >>= subst >> reflexivity
                       else by left >> intro "_" >>= injection >> contradiction
| (pos l₁) (neg l₂) := by left >> intron 1 >> contradiction
| (neg l₁)  all     := by left >> intron 1 >> contradiction
| (neg l₁) (pos l₂) := by left >> intron 1 >> contradiction
| (neg l₁) (neg l₂) := if H : l₁ = l₂
                       then by right >> get_local "H" >>= subst >> reflexivity
                       else by left >> intro "_" >>= injection >> contradiction

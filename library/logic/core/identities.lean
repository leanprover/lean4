-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad

-- logic.connectives.identities
-- ============================

-- Useful logical identities. In the absence of propositional extensionality, some of the
-- calculations use the type class support provided by logic.connectives.instances

import logic.core.instances

using relation

theorem or_right_comm (a b c : Prop) : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
calc
  (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) : or_assoc
    ... ↔ a ∨ (c ∨ b)       : {or_comm}
     ... ↔ (a ∨ c) ∨ b      : iff_symm or_assoc

theorem or_left_comm (a b c : Prop) : a ∨ (b ∨ c)↔ b ∨ (a ∨ c) :=
calc
  a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c : iff_symm or_assoc
    ... ↔ (b ∨ a) ∨ c       : {or_comm}
     ... ↔ b ∨ (a ∨ c)      : or_assoc

theorem and_right_comm (a b c : Prop) : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
calc
  (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) : and_assoc
    ... ↔ a ∧ (c ∧ b)       : {and_comm}
     ... ↔ (a ∧ c) ∧ b      : iff_symm and_assoc

theorem and_left_comm (a b c : Prop) : a ∧ (b ∧ c)↔ b ∧ (a ∧ c) :=
calc
  a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c : iff_symm and_assoc
    ... ↔ (b ∧ a) ∧ c       : {and_comm}
     ... ↔ b ∧ (a ∧ c)      : and_assoc

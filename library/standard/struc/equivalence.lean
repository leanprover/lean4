----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.connectives.prop

namespace equivalence
section
  parameter {A : Type}
  parameter p : A → A → Prop
  infix `∼`:50 := p
  definition reflexive  := ∀a, a ∼ a
  definition symmetric  := ∀a b, a ∼ b → b ∼ a
  definition transitive := ∀a b c, a ∼ b → b ∼ c → a ∼ c
end

inductive equivalence {A : Type} (p : A → A → Prop) : Prop :=
| equivalence_intro : reflexive p → symmetric p → transitive p → equivalence p

theorem equivalence_reflexive [instance] {A : Type} {p : A → A → Prop} (H : equivalence p) : reflexive p :=
equivalence_rec (λ r s t, r) H

theorem equivalence_symmetric [instance] {A : Type} {p : A → A → Prop} (H : equivalence p) : symmetric p :=
equivalence_rec (λ r s t, s) H

theorem equivalence_transitive [instance] {A : Type} {p : A → A → Prop} (H : equivalence p) : transitive p :=
equivalence_rec (λ r s t, t) H
end
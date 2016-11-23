/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import init.relation
universe variables u
class setoid (α : Type u) :=
(r : α → α → Prop) (iseqv : equivalence r)

namespace setoid
infix ` ≈ ` := setoid.r

variable {α : Type u}
variable [s : setoid α]
include s

@[refl] lemma refl (a : α) : a ≈ a :=
match setoid.iseqv α with
| ⟨h_refl, h_symm, h_trans⟩ := h_refl a
end

@[symm] lemma symm {a b : α} (hab : a ≈ b) : b ≈ a :=
match setoid.iseqv α with
| ⟨h_refl, h_symm, h_trans⟩ := h_symm hab
end

@[trans] lemma trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
match setoid.iseqv α with
| ⟨h_refl, h_symm, h_trans⟩ := h_trans hab hbc
end
end setoid

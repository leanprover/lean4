/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import init.relation
universe variables u
class setoid (A : Type u) :=
(r : A → A → Prop) (iseqv : equivalence r)

namespace setoid
  infix ` ≈ ` := setoid.r

  variable {A : Type u}
  variable [s : setoid A]
  include s

  attribute [refl]
  lemma refl (a : A) : a ≈ a :=
  match setoid.iseqv A with
  | ⟨H_refl, H_symm, H_trans⟩ := H_refl a
  end

  attribute [symm]
  lemma symm {a b : A} (Hab : a ≈ b) : b ≈ a :=
  match setoid.iseqv A with
  | ⟨H_refl, H_symm, H_trans⟩ := H_symm Hab
  end

  attribute [trans]
  lemma trans {a b c : A} (Hab : a ≈ b) (Hbc : b ≈ c) : a ≈ c :=
  match setoid.iseqv A with
  | ⟨H_refl, H_symm, H_trans⟩ := H_trans Hab Hbc
  end
end setoid

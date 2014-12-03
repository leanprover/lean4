-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer

import ..precategory.basic ..precategory.morphism
import hott.equiv hott.trunc

open precategory morphism is_equiv path truncation nat sigma sigma.ops

-- A category is a precategory extended by a witness,
-- that the function assigning to each isomorphism a path,
-- is an equivalecnce.
structure category [class] (ob : Type) extends (precategory ob) :=
  (iso_of_path_equiv : Π {a b : ob}, is_equiv (@iso_of_path ob (precategory.mk hom _ comp ID assoc id_left id_right) a b))

namespace category
  variables {ob : Type} {C : category ob} {a b : ob}
  include C

  -- Make iso_of_path_equiv a class instance
  -- TODO: Unsafe class instance?
  instance [persistent] iso_of_path_equiv

  definition path_of_iso {a b : ob} : a ≅ b → a ≈ b :=
  iso_of_path⁻¹

  definition foo {a b : ob} :

  definition ob_1_type : is_trunc -2 .+1 .+1 .+1 ob :=
  begin
    apply is_trunc_succ, intros (a, b),
    /-fapply trunc_equiv,
      exact (@path_of_iso ob C a b),
      apply inv_closed,
    exact sorry,-/
  end

end category

-- Bundled version of categories
inductive Category : Type := mk : Π (ob : Type), category ob → Category

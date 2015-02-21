-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer

import ..precategory.basic ..precategory.morphism ..precategory.iso

open precategory morphism is_equiv eq is_trunc nat sigma sigma.ops

-- A category is a precategory extended by a witness,
-- that the function assigning to each isomorphism a path,
-- is an equivalecnce.
structure category [class] (ob : Type) extends (precategory ob) :=
  (iso_of_path_equiv : Π {a b : ob}, is_equiv (@iso_of_path ob (precategory.mk hom _ comp ID assoc id_left id_right) a b))

attribute category [multiple-instances]

namespace category
  variables {ob : Type} {C : category ob} {a b : ob}
  include C

  -- Make iso_of_path_equiv a class instance
  -- TODO: Unsafe class instance?
  attribute iso_of_path_equiv [instance]

  definition path_of_iso {a b : ob} : a ≅ b → a = b :=
  iso_of_path⁻¹

  set_option apply.class_instance false -- disable class instance resolution in the apply tactic

  definition ob_1_type : is_trunc (succ nat.zero) ob :=
  begin
    apply is_trunc_succ_intro, intros (a, b),
    fapply is_trunc_is_equiv_closed,
          exact (@path_of_iso _ _ a b),
        apply is_equiv_inv,
    apply is_hset_iso,
  end

end category

-- Bundled version of categories

structure Category : Type :=
  (objects : Type)
  (category_instance : category objects)

namespace category
  definition Mk {ob} (C) : Category := Category.mk ob C
  --definition MK (a b c d e f g h i) : Category := Category.mk a (category.mk b c d e f g h i)

  definition objects [coercion] [reducible] := Category.objects
  definition category_instance [instance] [coercion] [reducible] := Category.category_instance

end category

open category

protected definition Category.eta (C : Category) : Category.mk C C = C :=
Category.rec (λob c, idp) C

/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.constructions
Authors: Floris van Doorn
-/

import .basic algebra.precategory.constructions

open eq prod eq eq.ops equiv is_trunc funext pi category.ops morphism category

namespace category

  section hset
  definition is_category_hset (a b : Precategory_hset) : is_equiv (@iso_of_path _ _ a b) :=
  sorry

  definition category_hset [reducible] [instance] : category hset :=
  category.mk' hset precategory_hset is_category_hset

  definition Category_hset [reducible] : Category :=
  Category.mk hset category_hset

  definition isomorphic_hset_eq_equiv (a b : Category_hset) : (a ≅ b) = (a ≃ b) := sorry

  end hset
  namespace ops
    abbreviation set := Category_hset
  end ops

end category

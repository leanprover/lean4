/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.list.basic

namespace list
structure as_type {A : Type} (l : list A) : Type :=
(value : A) (is_member : value ∈ l)

namespace as_type
notation `⟪`:max l `⟫`:0 := as_type l

definition lval {A : Type} (a : A) {l : list A} (m : a ∈ l) : ⟪l⟫ :=
mk a m
end as_type
end list

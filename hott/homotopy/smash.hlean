/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Smash Product of Types
-/

import hit.pushout .wedge .cofiber .susp .sphere

open eq pushout prod pointed Pointed

definition product_of_wedge (A B : Type*) : Wedge A B →* A ×* B :=
begin
  fconstructor,
  intro x, induction x with [a, b], exact (a, point B), exact (point A, b), 
  do 2 reflexivity
end

definition Smash (A B : Type*) := Cofiber (product_of_wedge A B)

open sphere susp

namespace smash

  definition susp_equiv_circle_smash (X : Type*) : Susp X ≃* Smash (Sphere 1) X :=
  sorry  

end smash

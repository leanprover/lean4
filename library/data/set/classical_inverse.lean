/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer

Using classical logic, defines an inverse function.
-/
import .function .map
import logic.choice
open eq.ops

namespace set

variables {X Y : Type}

noncomputable definition inv_fun (f : X → Y) (a : set X) (dflt : X) (y : Y) : X :=
if H : ∃₀ x ∈ a, f x = y then some H else dflt

theorem inv_fun_pos {f : X → Y} {a : set X} {dflt : X} {y : Y}
  (H : ∃₀ x ∈ a, f x = y) : (inv_fun f a dflt y ∈ a) ∧ (f (inv_fun f a dflt y) = y) :=
have H1 : inv_fun f a dflt y = some H, from dif_pos H,
H1⁻¹ ▸ some_spec H

theorem inv_fun_neg {f : X → Y} {a : set X} {dflt : X} {y : Y}
  (H : ¬ ∃₀ x ∈ a, f x = y) : inv_fun f a dflt y = dflt :=
dif_neg H

variables {f : X → Y} {a : set X} {b : set Y}

theorem maps_to_inv_fun {dflt : X} (dflta : dflt ∈ a) :
  maps_to (inv_fun f a dflt) b a :=
let f' := inv_fun f a dflt in
take y,
assume yb : y ∈ b,
show f' y ∈ a, from
  by_cases
    (assume H : ∃₀ x ∈ a, f x = y,
      and.left (inv_fun_pos H))
    (assume H : ¬ ∃₀ x ∈ a, f x = y,
      (inv_fun_neg H)⁻¹ ▸ dflta)

theorem left_inv_on_inv_fun_of_inj_on (dflt : X) (H : inj_on f a) :
  left_inv_on (inv_fun f a dflt) f a :=
let f' := inv_fun f a dflt in
take x,
assume xa : x ∈ a,
have H1 : ∃₀ x' ∈ a, f x' = f x, from exists.intro x (and.intro xa rfl),
have H2 : f' (f x) ∈ a ∧ f (f' (f x)) = f x, from inv_fun_pos H1,
show f' (f x) = x, from H (and.left H2) xa (and.right H2)

theorem right_inv_on_inv_fun_of_surj_on (dflt : X) (H : surj_on f a b) :
  right_inv_on (inv_fun f a dflt) f b :=
let f' := inv_fun f a dflt in
take y,
assume yb: y ∈ b,
obtain x (Hx : x ∈ a ∧ f x = y), from H yb,
have Hy : f' y ∈ a ∧ f (f' y) = y, from inv_fun_pos (exists.intro x Hx),
and.right Hy

end set

open set

namespace map

variables {X Y : Type} {a : set X} {b : set Y}

protected noncomputable definition inverse (f : map a b) {dflt : X} (dflta : dflt ∈ a) :=
map.mk (inv_fun f a dflt) (@maps_to_inv_fun _ _ _ _ b _ dflta)

theorem left_inverse_inverse {f : map a b} {dflt : X} (dflta : dflt ∈ a) (H : map.injective f) :
  map.left_inverse (map.inverse f dflta) f :=
left_inv_on_inv_fun_of_inj_on dflt H

theorem right_inverse_inverse {f : map a b} {dflt : X} (dflta : dflt ∈ a) (H : map.surjective f) :
  map.right_inverse (map.inverse f dflta) f :=
right_inv_on_inv_fun_of_surj_on dflt H

theorem is_inverse_inverse {f : map a b} {dflt : X} (dflta : dflt ∈ a) (H : map.bijective f) :
map.is_inverse (map.inverse f dflta) f :=
and.intro
  (left_inverse_inverse dflta (and.left H))
  (right_inverse_inverse dflta (and.right H))

end map

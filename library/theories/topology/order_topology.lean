/-
Copyright (c) 2016 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross

The order topology.
-/
import data.set theories.topology.basic algebra.interval
open algebra eq.ops set interval topology

namespace order_topology

variables {X : Type} [linear_strong_order_pair X]

definition linorder_generators : set (set X) := {y | ∃ a, y = '(a, ∞) } ∪ {y | ∃ a, y = '(-∞, a)}

definition linorder_topology [instance] [reducible] : topology X :=
  topology.generated_by linorder_generators

theorem Open_Ioi {a : X} : Open '(a, ∞) :=
(generators_mem_topology_generated_by linorder_generators) (!mem_unionl (exists.intro a rfl))

theorem Open_Iio {a : X} : Open '(-∞, a) :=
(generators_mem_topology_generated_by linorder_generators) (!mem_unionr (exists.intro a rfl))

theorem closed_Ici (a : X) : closed '[a,∞) :=
!compl_Ici⁻¹ ▸ Open_Iio

theorem closed_Iic (a : X) : closed '(-∞,a] :=
have '(a, ∞) = -'(-∞,a], from ext(take x, iff.intro
  (assume H, not_le_of_gt H)
  (assume H, lt_of_not_ge H)),
this ▸ Open_Ioi

theorem Open_Ioo (a b : X) : Open '(a, b) :=
Open_inter !Open_Ioi !Open_Iio

theorem closed_Icc (a b : X) : closed '[a, b] :=
closed_inter !closed_Ici !closed_Iic

section
  open classical

  theorem linorder_separation {x y : X} :
    x < y → ∃ a b, (x < a ∧ b < y) ∧ '(-∞, a) ∩ '(b, ∞) = ∅ :=
  suppose x < y,
  if H1 : ∃ z, x < z ∧ z < y then
    obtain z (Hz : x < z ∧ z < y), from H1,
    have '(-∞, z) ∩ '(z, ∞) = ∅, from ext (take r, iff.intro
      (assume H, absurd (!lt.trans (and.elim_left H) (and.elim_right H)) !lt.irrefl)
      (assume H, !not.elim !not_mem_empty H)),
    exists.intro z (exists.intro z (and.intro Hz this))
  else
    have '(-∞, y) ∩ '(x, ∞) = ∅, from ext(take r, iff.intro
      (assume H, absurd (exists.intro r (iff.elim_left and.comm H)) H1)
      (assume H, !not.elim !not_mem_empty H)),
    exists.intro y (exists.intro x (and.intro (and.intro `x < y` `x < y`) this))
end

protected definition T2_space.of_linorder_topology [reducible] [trans_instance] :
  T2_space X :=
⦃ T2_space, linorder_topology,
  T2 := abstract
         take x y, assume H,
         or.elim (lt_or_gt_of_ne H)
           (assume H,
            obtain a [b Hab], from linorder_separation H,
            show _, from exists.intro '(-∞, a) (exists.intro '(b, ∞)
              (and.intro Open_Iio (and.intro Open_Ioi (iff.elim_left and.assoc Hab)))))
           (assume H,
            obtain a [b Hab], from linorder_separation H,
            have Hx : x ∈ '(b, ∞), from and.elim_right (and.elim_left Hab),
            have Hy : y ∈ '(-∞, a), from and.elim_left (and.elim_left Hab),
            have Hi : '(b, ∞) ∩ '(-∞, a) = ∅, from !inter_comm ▸ (and.elim_right Hab),
            have (Open '(b,∞)) ∧ (Open '(-∞, a)) ∧ x ∈ '(b, ∞) ∧ y ∈ '(-∞, a) ∧
                   '(b, ∞) ∩ '(-∞, a) = ∅, from
             and.intro Open_Ioi (and.intro Open_Iio (and.intro Hx (and.intro Hy Hi))),
           show _, from exists.intro '(b,∞) (exists.intro '(-∞, a) this))
        end ⦄

end order_topology

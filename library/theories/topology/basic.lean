/-
Copyright (c) 2015 Jacob Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Gross, Jeremy Avigad

Open and closed sets, seperation axioms and generated topologies.
-/
import data.set data.nat
open algebra eq.ops set nat

structure topology [class] (X : Type) :=
  (opens : set (set X))
  (univ_mem_opens : univ ∈ opens)
  (sUnion_mem_opens : ∀ {S : set (set X)}, S ⊆ opens → ⋃₀ S ∈ opens)
  (inter_mem_opens : ∀₀ s ∈ opens, ∀₀ t ∈ opens, s ∩ t ∈ opens)

namespace topology

variables {X : Type} [topology X]

/- open sets -/

definition Open (s : set X) : Prop := s ∈ opens X

theorem Open_empty : Open (∅ : set X) :=
have ∅ ⊆ opens X, from empty_subset _,
have ⋃₀ ∅ ∈ opens X, from sUnion_mem_opens this,
show ∅ ∈ opens X, using this, by rewrite -sUnion_empty; apply this

theorem Open_univ : Open (univ : set X) :=
univ_mem_opens X

theorem Open_sUnion {S : set (set X)} (H : ∀₀ t ∈ S, Open t) : Open (⋃₀ S) :=
sUnion_mem_opens H

theorem Open_Union {I : Type} {s : I → set X} (H : ∀ i, Open (s i)) : Open (⋃ i, s i) :=
have ∀₀ t ∈ s ' univ, Open t,
  from take t, suppose t ∈ s ' univ,
    obtain i [univi (Hi : s i = t)], from this,
    show Open t, by rewrite -Hi; exact H i,
using this, by rewrite Union_eq_sUnion_image; apply Open_sUnion this

theorem Open_union {s t : set X} (Hs : Open s) (Ht : Open t) : Open (s ∪ t) :=
have ∀ i, Open (bin_ext s t i), by intro i; cases i; exact Hs; exact Ht,
show Open (s ∪ t), using this, by rewrite -Union_bin_ext; exact Open_Union this

theorem Open_inter {s t : set X} (Hs : Open s) (Ht : Open t) : Open (s ∩ t) :=
inter_mem_opens X Hs Ht

theorem Open_sInter_of_finite {s : set (set X)} [fins : finite s] (H : ∀₀ t ∈ s, Open t) :
  Open (⋂₀ s) :=
begin
  induction fins with a s fins anins ih,
    {rewrite sInter_empty, exact Open_univ},
  rewrite sInter_insert,
  apply Open_inter,
    show Open a, from H (mem_insert a s),
  apply ih, intros t ts,
  show Open t, from H (mem_insert_of_mem a ts)
end

/- closed sets -/

definition closed [reducible] (s : set X) : Prop := Open (-s)

theorem closed_iff_Open_comp (s : set X) : closed s ↔ Open (-s) := !iff.refl

theorem Open_iff_closed_comp (s : set X) : Open s ↔ closed (-s) :=
by rewrite [closed_iff_Open_comp, comp_comp]

theorem closed_comp {s : set X} (H : Open s) : closed (-s) :=
by rewrite [-Open_iff_closed_comp]; apply H

theorem closed_empty : closed (∅ : set X) :=
by rewrite [↑closed, comp_empty]; exact Open_univ

theorem closed_univ : closed (univ : set X) :=
by rewrite [↑closed, comp_univ]; exact Open_empty

theorem closed_sInter {S : set (set X)} (H : ∀₀ t ∈ S, closed t) : closed (⋂₀ S) :=
begin
  rewrite [↑closed, comp_sInter],
  apply Open_sUnion,
  intro t,
  rewrite [mem_image_complement, Open_iff_closed_comp],
  apply H
end

theorem closed_Inter {I : Type} {s : I → set X} (H : ∀ i, closed (s i : set X)) :
  closed (⋂ i, s i) :=
by rewrite [↑closed, comp_Inter]; apply Open_Union; apply H

theorem closed_inter {s t : set X} (Hs : closed s) (Ht : closed t) : closed (s ∩ t) :=
by rewrite [↑closed, comp_inter]; apply Open_union; apply Hs; apply Ht

theorem closed_union {s t : set X} (Hs : closed s) (Ht : closed t) : closed (s ∪ t) :=
by rewrite [↑closed, comp_union]; apply Open_inter; apply Hs; apply Ht

theorem closed_sUnion_of_finite {s : set (set X)} [fins : finite s] (H : ∀₀ t ∈ s, closed t) :
  closed (⋂₀ s) :=
begin
  rewrite [↑closed, comp_sInter],
  apply Open_sUnion,
  intro t,
  rewrite [mem_image_complement, Open_iff_closed_comp],
  apply H
end

theorem open_diff {s t : set X} (Hs : Open s) (Ht : closed t) : Open (s \ t) :=
Open_inter Hs Ht

theorem closed_diff {s t : set X} (Hs : closed s) (Ht : Open t) : closed (s \ t) :=
closed_inter Hs (closed_comp Ht)

end topology

/- separation -/

structure T0_space [class] (X : Type) extends topology X :=
 (T0 : ∀ {x y}, x ≠ y → ∃ U, U ∈ opens ∧ ¬(x ∈ U ↔ y ∈ U))

namespace topology
  variables {X : Type} [T0_space X]

  theorem T0 {x y : X} (H : x ≠ y) : ∃ U, Open U ∧ ¬(x ∈ U ↔ y ∈ U) :=
  T0_space.T0 H
end topology

structure T1_space [class] (X : Type) extends topology X :=
  (T1 : ∀ {x y}, x ≠ y → ∃ U, U ∈ opens ∧ x ∈ U ∧ y ∉ U)

protected definition T0_space.of_T1 [reducible] [trans_instance] {X : Type} [T : T1_space X] :
  T0_space X :=
⦃T0_space, T,
  T0 := abstract
          take x y, assume H,
          obtain U [Uopens [xU ynU]], from T1_space.T1 H,
          exists.intro U (and.intro Uopens
            (show ¬ (x ∈ U ↔ y ∈ U), from assume H, ynU (iff.mp H xU)))
        end ⦄

namespace topology
  variables {X : Type} [T1_space X]

  theorem T1 {x y : X} (H : x ≠ y) : ∃ U, Open U ∧ x ∈ U ∧ y ∉ U :=
  T1_space.T1 H
end topology

structure T2_space [class] (X : Type) extends topology X :=
  (T2 : ∀ {x y}, x ≠ y → ∃ U V, U ∈ opens ∧ V ∈ opens ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅)

protected definition T1_space.of_T2 [reducible] [trans_instance] {X : Type} [T : T2_space X] :
  T1_space X :=
⦃T1_space, T,
  T1 := abstract
          take x y, assume H,
          obtain U [V [Uopens [Vopens [xU [yV UVempty]]]]], from T2_space.T2 H,
          exists.intro U (and.intro Uopens (and.intro xU
            (show y ∉ U, from assume yU,
              have y ∈ U ∩ V, from and.intro yU yV,
              show y ∈ ∅, from UVempty ▸ this)))
        end ⦄

namespace topology
  variables {X : Type} [T2_space X]

  theorem T2 {x y : X} (H : x ≠ y) : ∃ U V, Open U ∧ Open V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅ :=
  T2_space.T2 H
end topology

structure perfect_space [class] (X : Type) extends topology X :=
  (perfect : ∀ x, '{x} ∉ opens)

/- topology generated by a set -/

namespace topology

inductive opens_generated_by {X : Type} (B : set (set X)) : set X → Prop :=
| generators_mem : ∀ ⦃s : set X⦄, s ∈ B → opens_generated_by B s
| univ_mem       : opens_generated_by B univ
| inter_mem      : ∀ ⦃s t⦄, opens_generated_by B s → opens_generated_by B t →
                    opens_generated_by B (s ∩ t)
| sUnion_mem     : ∀ ⦃S : set (set X)⦄, S ⊆ opens_generated_by B → opens_generated_by B (⋃₀ S)

protected definition generated_by [instance] [reducible] {X : Type} (B : set (set X)) : topology X :=
⦃topology,
  opens            := opens_generated_by B,
  univ_mem_opens   := opens_generated_by.univ_mem B,
  inter_mem_opens  := λ s Hs t Ht, opens_generated_by.inter_mem Hs Ht,
  sUnion_mem_opens := opens_generated_by.sUnion_mem
⦄

theorem generators_mem_topology_generated_by {X : Type} (B : set (set X)) :
  let T := topology.generated_by B in
  ∀₀ s ∈ B, @Open _ T s :=
λ s H, opens_generated_by.generators_mem H

theorem opens_generated_by_initial {X : Type} {B : set (set X)} {T : topology X} (H : B ⊆ @opens _ T) :
  opens_generated_by B ⊆ @opens _ T :=
begin
  intro s Hs,
  induction Hs with s sB s t os ot soX toX S SB SOX,
    {exact H sB},
    {exact univ_mem_opens X},
    {exact inter_mem_opens X soX toX},
  exact sUnion_mem_opens SOX
end

theorem topology_generated_by_initial {X : Type} {B : set (set X)} {T : topology X}
    (H : ∀₀ s ∈ B, @Open _ T s) {s : set X} (H1 : @Open _ (topology.generated_by B) s) :
  @Open _ T s :=
opens_generated_by_initial H H1

end topology

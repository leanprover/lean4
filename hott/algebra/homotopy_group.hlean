/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
-/

import types.pointed .trunc_group .hott types.trunc

open nat eq pointed trunc is_trunc algebra

namespace eq

  definition homotopy_group [reducible] (n : ℕ) (A : Type*) : Type :=
  trunc 0 (Ω[n] A)

  notation `π[`:95 n:0 `] `:0 A:95 := homotopy_group n A

  definition pointed_homotopy_group [instance] [constructor] (n : ℕ) (A : Type*)
    : pointed (π[n] A) :=
  pointed.mk (tr rfln)

  definition group_homotopy_group [instance] [constructor] (n : ℕ) (A : Type*)
    : group (π[succ n] A) :=
  trunc_group concat inverse idp con.assoc idp_con con_idp con.left_inv

  definition comm_group_homotopy_group [constructor] (n : ℕ) (A : Type*)
    : comm_group (π[succ (succ n)] A) :=
  trunc_comm_group concat inverse idp con.assoc idp_con con_idp con.left_inv eckmann_hilton

  local attribute comm_group_homotopy_group [instance]

  definition Pointed_homotopy_group [constructor] (n : ℕ) (A : Type*) : Type* :=
  Pointed.mk (π[n] A)

  definition Group_homotopy_group [constructor] (n : ℕ) (A : Type*) : Group :=
  Group.mk (π[succ n] A) _

  definition CommGroup_homotopy_group [constructor] (n : ℕ) (A : Type*) : CommGroup :=
  CommGroup.mk (π[succ (succ n)] A) _

  definition fundamental_group [constructor] (A : Type*) : Group :=
  Group_homotopy_group zero A

  notation `πP[`:95  n:0    `] `:0 A:95 := Pointed_homotopy_group n A
  notation `πG[`:95  n:0 ` +1] `:0 A:95 := Group_homotopy_group n A
  notation `πaG[`:95 n:0 ` +2] `:0 A:95 := CommGroup_homotopy_group n A

  prefix `π₁`:95 := fundamental_group

  open equiv unit
  theorem trivial_homotopy_of_is_hset (A : Type*) [H : is_hset A] (n : ℕ) : πG[n+1] A = G0 :=
  begin
    apply trivial_group_of_is_contr,
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply is_trunc_succ_succ_of_is_hset
  end

  definition homotopy_group_succ_out (A : Type*) (n : ℕ) : πG[ n +1] A = π₁ Ω[n] A := idp

  definition homotopy_group_succ_in (A : Type*) (n : ℕ) : πG[succ n +1] A = πG[n +1] Ω A :=
  begin
    fapply Group_eq,
    { apply equiv_of_eq, exact ap (λ(X : Type*), trunc 0 X) (loop_space_succ_eq_in A (succ n))},
    { exact abstract [irreducible] begin refine trunc.rec _, intro p, refine trunc.rec _, intro q,
      rewrite [▸*,-+tr_eq_cast_ap, +trunc_transport, ↑[group_homotopy_group, group.to_monoid,
        monoid.to_semigroup, semigroup.to_has_mul, trunc_mul], trunc_transport], apply ap tr,
      apply loop_space_succ_eq_in_concat end end},
  end

  definition homotopy_group_add (A : Type*) (n m : ℕ) : πG[n+m +1] A = πG[n +1] Ω[m] A :=
  begin
    revert A, induction m with m IH: intro A,
    { reflexivity},
    { esimp [Iterated_loop_space, nat.add], refine !homotopy_group_succ_in ⬝ _, refine !IH ⬝ _,
      exact ap (Group_homotopy_group n) !loop_space_succ_eq_in⁻¹}
  end

  theorem trivial_homotopy_of_is_hset_loop_space {A : Type*} {n : ℕ} (m : ℕ) (H : is_hset (Ω[n] A))
    : πG[m+n+1] A = G0 :=
  !homotopy_group_add ⬝ !trivial_homotopy_of_is_hset

end eq

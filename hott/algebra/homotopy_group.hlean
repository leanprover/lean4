/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
-/

import .trunc_group .hott types.trunc

open nat eq pointed trunc is_trunc algebra

namespace eq

  definition phomotopy_group [constructor] (n : ℕ) (A : Type*) : Set* :=
  ptrunc 0 (Ω[n] A)

  definition homotopy_group [reducible] (n : ℕ) (A : Type*) : Type :=
  phomotopy_group n A

  notation `π*[`:95  n:0    `] `:0 A:95 := phomotopy_group n A
  notation `π[`:95 n:0 `] `:0 A:95 := homotopy_group n A

  definition group_homotopy_group [instance] [constructor] (n : ℕ) (A : Type*)
    : group (π[succ n] A) :=
  trunc_group concat inverse idp con.assoc idp_con con_idp con.left_inv

  definition comm_group_homotopy_group [constructor] (n : ℕ) (A : Type*)
    : comm_group (π[succ (succ n)] A) :=
  trunc_comm_group concat inverse idp con.assoc idp_con con_idp con.left_inv eckmann_hilton

  local attribute comm_group_homotopy_group [instance]

  definition ghomotopy_group [constructor] (n : ℕ) (A : Type*) : Group :=
  Group.mk (π[succ n] A) _

  definition cghomotopy_group [constructor] (n : ℕ) (A : Type*) : CommGroup :=
  CommGroup.mk (π[succ (succ n)] A) _

  definition fundamental_group [constructor] (A : Type*) : Group :=
  ghomotopy_group zero A

  notation `πg[`:95  n:0 ` +1] `:0 A:95 := ghomotopy_group n A
  notation `πag[`:95 n:0 ` +2] `:0 A:95 := cghomotopy_group n A

  prefix `π₁`:95 := fundamental_group

  definition phomotopy_group_pequiv [constructor] (n : ℕ) {A B : Type*} (H : A ≃* B)
    : π*[n] A ≃* π*[n] B :=
  ptrunc_pequiv 0 (iterated_loop_space_pequiv n H)

  set_option pp.coercions true
  set_option pp.numerals false
  definition phomotopy_group_pequiv_loop_ptrunc [constructor] (k : ℕ) (A : Type*) :
    π*[k] A ≃* Ω[k] (ptrunc k A) :=
  begin
    refine !iterated_loop_ptrunc_pequiv⁻¹ᵉ* ⬝e* _,
    rewrite [trunc_index.zero_add]
  end

  open equiv unit
  theorem trivial_homotopy_of_is_set (A : Type*) [H : is_set A] (n : ℕ) : πg[n+1] A = G0 :=
  begin
    apply trivial_group_of_is_contr,
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply is_trunc_succ_succ_of_is_set
  end

  definition phomotopy_group_succ_out (A : Type*) (n : ℕ) : π*[n + 1] A = π₁ Ω[n] A := idp

  definition phomotopy_group_succ_in (A : Type*) (n : ℕ) : π*[n + 1] A = π*[n] Ω A :=
  ap (ptrunc 0) (loop_space_succ_eq_in A n)

  definition ghomotopy_group_succ_out (A : Type*) (n : ℕ) : πg[n +1] A = π₁ Ω[n] A := idp

  definition ghomotopy_group_succ_in (A : Type*) (n : ℕ) : πg[succ n +1] A = πg[n +1] Ω A :=
  begin
    fapply Group_eq,
    { apply equiv_of_eq, exact ap (ptrunc 0) (loop_space_succ_eq_in A (succ n))},
    { exact abstract [irreducible] begin refine trunc.rec _, intro p, refine trunc.rec _, intro q,
      rewrite [▸*,-+tr_eq_cast_ap, +trunc_transport], refine !trunc_transport ⬝ _, apply ap tr,
      apply loop_space_succ_eq_in_concat end end},
  end

  definition homotopy_group_add (A : Type*) (n m : ℕ) : πg[n+m +1] A = πg[n +1] Ω[m] A :=
  begin
    revert A, induction m with m IH: intro A,
    { reflexivity},
    { esimp [iterated_ploop_space, nat.add], refine !ghomotopy_group_succ_in ⬝ _, refine !IH ⬝ _,
      exact ap (ghomotopy_group n) !loop_space_succ_eq_in⁻¹}
  end

  theorem trivial_homotopy_add_of_is_set_loop_space {A : Type*} {n : ℕ} (m : ℕ)
    (H : is_set (Ω[n] A)) : πg[m+n+1] A = G0 :=
  !homotopy_group_add ⬝ !trivial_homotopy_of_is_set

  theorem trivial_homotopy_le_of_is_set_loop_space {A : Type*} {n : ℕ} (m : ℕ) (H1 : n ≤ m)
    (H2 : is_set (Ω[n] A)) : πg[m+1] A = G0 :=
  obtain (k : ℕ) (p : n + k = m), from le.elim H1,
  ap (λx, πg[x+1] A) (p⁻¹ ⬝ add.comm n k) ⬝ trivial_homotopy_add_of_is_set_loop_space k H2

  definition phomotopy_group_functor [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    : π*[n] A →* π*[n] B :=
  ptrunc_functor 0 (apn n f)

  definition homotopy_group_functor (n : ℕ) {A B : Type*} (f : A →* B) : π[n] A → π[n] B :=
  phomotopy_group_functor n f

  notation `π→*[`:95 n:0 `] `:0 f:95 := phomotopy_group_functor n f
  notation `π→[`:95  n:0 `] `:0 f:95 :=  homotopy_group_functor n f

  definition tinverse [constructor] {X : Type*} : π*[1] X →* π*[1] X :=
  ptrunc_functor 0 pinverse

  definition ptrunc_functor_pinverse [constructor] {X : Type*}
    : ptrunc_functor 0 (@pinverse X) ~* @tinverse X :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { reflexivity}
  end

  definition phomotopy_group_functor_mul [constructor] (n : ℕ) {A B : Type*} (g : A →* B)
    (p q : πg[n+1] A) :
    (π→[n + 1] g) (p *[πg[n+1] A] q) = (π→[n + 1] g) p *[πg[n+1] B] (π→[n + 1] g) q :=
  begin
    unfold [ghomotopy_group, homotopy_group] at *,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ p, clear p, intro p,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ q, clear q, intro q,
    apply ap tr, apply apn_con
  end




end eq

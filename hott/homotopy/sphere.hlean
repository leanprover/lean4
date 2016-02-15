/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the n-spheres
-/

import .susp types.trunc

open eq nat susp bool is_trunc unit pointed

/-
  We can define spheres with the following possible indices:
  - trunc_index (defining S^-2 = S^-1 = empty)
  - nat (forgetting that S^-1 = empty)
  - nat, but counting wrong (S^0 = empty, S^1 = bool, ...)
  - some new type "integers >= -1"
  We choose the last option here.
-/

 /- Sphere levels -/

inductive sphere_index : Type₀ :=
| minus_one : sphere_index
| succ : sphere_index → sphere_index

namespace trunc_index
  definition sub_one [reducible] (n : sphere_index) : trunc_index :=
  sphere_index.rec_on n -2 (λ n k, k.+1)
  postfix `.-1`:(max+1) := sub_one
end trunc_index

namespace sphere_index
  /-
     notation for sphere_index is -1, 0, 1, ...
     from 0 and up this comes from a coercion from num to sphere_index (via nat)
  -/

  definition has_zero_sphere_index [instance] [reducible] : has_zero sphere_index :=
  has_zero.mk (succ minus_one)

  definition has_one_sphere_index [instance] [reducible] : has_one sphere_index :=
  has_one.mk (succ (succ minus_one))

  postfix `.+1`:(max+1) := sphere_index.succ
  postfix `.+2`:(max+1) := λ(n : sphere_index), (n .+1 .+1)
  notation `-1` := minus_one
  notation `ℕ₋₁` := sphere_index

  definition add (n m : sphere_index) : sphere_index :=
  sphere_index.rec_on m n (λ k l, l .+1)

  definition leq (n m : sphere_index) : Type₀ :=
  sphere_index.rec_on n (λm, unit) (λ n p m, sphere_index.rec_on m (λ p, empty) (λ m q p, p m) p) m

  infix `+1+`:65 := sphere_index.add

  definition has_le_sphere_index [instance] [reducible] : has_le sphere_index :=
  has_le.mk leq

  definition succ_le_succ {n m : sphere_index} (H : n ≤ m) : n.+1 ≤ m.+1 := proof H qed
  definition le_of_succ_le_succ {n m : sphere_index} (H : n.+1 ≤ m.+1) : n ≤ m := proof H qed
  definition minus_two_le (n : sphere_index) : -1 ≤ n := star
  definition empty_of_succ_le_minus_two {n : sphere_index} (H : n .+1 ≤ -1) : empty := H

  definition of_nat [coercion] [reducible] (n : nat) : sphere_index :=
  (nat.rec_on n -1 (λ n k, k.+1)).+1

  definition trunc_index_of_sphere_index [coercion] [reducible] (n : sphere_index) : trunc_index :=
  (sphere_index.rec_on n -2 (λ n k, k.+1)).+1

  definition sub_one [reducible] (n : ℕ) : sphere_index :=
  nat.rec_on n -1 (λ n k, k.+1)

  postfix `.-1`:(max+1) := sub_one

  open trunc_index
  definition sub_two_eq_sub_one_sub_one (n : ℕ) : n.-2 = n.-1.-1 :=
  nat.rec_on n idp (λn p, ap trunc_index.succ p)

end sphere_index

open sphere_index equiv

definition sphere : sphere_index → Type₀
| -1   := empty
| n.+1 := susp (sphere n)

namespace sphere

  definition base {n : ℕ} : sphere n := north
  definition pointed_sphere [instance] [constructor] (n : ℕ) : pointed (sphere n) :=
  pointed.mk base
  definition psphere [constructor] (n : ℕ) : Type* := pointed.mk' (sphere n)

  namespace ops
    abbreviation S := sphere
    notation `S.` := psphere
  end ops
  open sphere.ops

  definition equator (n : ℕ) : map₊ (S. n) (Ω (S. (succ n))) :=
  pmap.mk (λa, merid a ⬝ (merid base)⁻¹) !con.right_inv

  definition surf {n : ℕ} : Ω[n] S. n :=
  nat.rec_on n (proof base qed)
               (begin intro m s, refine cast _ (apn m (equator m) s),
                      exact ap carrier !loop_space_succ_eq_in⁻¹ end)


  definition bool_of_sphere : S 0 → bool :=
  proof susp.rec ff tt (λx, empty.elim x) qed

  definition sphere_of_bool : bool → S 0
  | ff := proof north qed
  | tt := proof south qed

  definition sphere_equiv_bool : S 0 ≃ bool :=
  equiv.MK bool_of_sphere
           sphere_of_bool
           (λb, match b with | tt := idp | ff := idp end)
           (λx, proof susp.rec_on x idp idp (empty.rec _) qed)

  definition sphere_eq_bool : S 0 = bool :=
  ua sphere_equiv_bool

  definition sphere_eq_bool_pointed : S. 0 = pbool :=
  pType_eq sphere_equiv_bool idp

  -- TODO: the commented-out part makes the forward function below "apn _ surf"
  definition pmap_sphere (A : Type*) (n : ℕ) : map₊ (S. n) A ≃ Ω[n] A :=
  begin
    -- fapply equiv_change_fun,
    -- {
      revert A, induction n with n IH: intro A,
      { rewrite [sphere_eq_bool_pointed], apply pmap_bool_equiv},
      { refine susp_adjoint_loop (S. n) A ⬝e !IH ⬝e _, rewrite [loop_space_succ_eq_in]}
    -- },
    -- { intro f, exact apn n f surf},
    -- { revert A, induction n with n IH: intro A f,
    --   { exact sorry},
    --   { exact sorry}}
  end

  protected definition elim {n : ℕ} {P : Type*} (p : Ω[n] P) : map₊ (S. n) P :=
  to_inv !pmap_sphere p

  -- definition elim_surf {n : ℕ} {P : Type*} (p : Ω[n] P) : apn n (sphere.elim p) surf = p :=
  -- begin
  --   induction n with n IH,
  --   { esimp [apn,surf,sphere.elim,pmap_sphere], apply sorry},
  --   { apply sorry}
  -- end

end sphere

open sphere sphere.ops

namespace is_trunc
  open trunc_index
  variables {n : ℕ} {A : Type}
  definition is_trunc_of_pmap_sphere_constant
    (H : Π(a : A) (f : map₊ (S. n) (pointed.Mk a)) (x : S n), f x = f base) : is_trunc (n.-2.+1) A :=
  begin
    apply iff.elim_right !is_trunc_iff_is_contr_loop,
    intro a,
    apply is_trunc_equiv_closed, apply pmap_sphere,
    fapply is_contr.mk,
    { exact pmap.mk (λx, a) idp},
    { intro f, fapply pmap_eq,
      { intro x, esimp, refine !respect_pt⁻¹ ⬝ (!H ⬝ !H⁻¹)},
      { rewrite [▸*,con.right_inv,▸*,con.left_inv]}}
  end

  definition is_trunc_iff_map_sphere_constant
    (H : Π(f : S n → A) (x : S n), f x = f base) : is_trunc (n.-2.+1) A :=
  begin
    apply is_trunc_of_pmap_sphere_constant,
    intros, cases f with f p, esimp at *, apply H
  end

  definition pmap_sphere_constant_of_is_trunc' [H : is_trunc (n.-2.+1) A]
    (a : A) (f : map₊ (S. n) (pointed.Mk a)) (x : S n) : f x = f base :=
  begin
    let H' := iff.elim_left (is_trunc_iff_is_contr_loop n A) H a,
    note H'' := @is_trunc_equiv_closed_rev _ _ _ !pmap_sphere H',
    assert p : (f = pmap.mk (λx, f base) (respect_pt f)),
      apply is_prop.elim,
    exact ap10 (ap pmap.to_fun p) x
  end

  definition pmap_sphere_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (a : A) (f : map₊ (S. n) (pointed.Mk a)) (x y : S n) : f x = f y :=
  let H := pmap_sphere_constant_of_is_trunc' a f in !H ⬝ !H⁻¹

  definition map_sphere_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (f : S n → A) (x y : S n) : f x = f y :=
  pmap_sphere_constant_of_is_trunc (f base) (pmap.mk f idp) x y

  definition map_sphere_constant_of_is_trunc_self [H : is_trunc (n.-2.+1) A]
    (f : S n → A) (x : S n) : map_sphere_constant_of_is_trunc f x x = idp :=
  !con.right_inv

end is_trunc

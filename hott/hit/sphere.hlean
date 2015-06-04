/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the n-spheres
-/

import .suspension types.trunc

open eq nat suspension bool is_trunc unit pointed

/-
  We can define spheres with the following possible indices:
  - trunc_index (defining S^-2 = S^-1 = empty)
  - nat (forgetting that S^1 = empty)
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
  postfix `.+1`:(max+1) := sphere_index.succ
  postfix `.+2`:(max+1) := λ(n : sphere_index), (n .+1 .+1)
  notation `-1` := minus_one
  export [coercions] nat

  definition add (n m : sphere_index) : sphere_index :=
  sphere_index.rec_on m n (λ k l, l .+1)

  definition leq (n m : sphere_index) : Type₀ :=
  sphere_index.rec_on n (λm, unit) (λ n p m, sphere_index.rec_on m (λ p, empty) (λ m q p, p m) p) m

  infix `+1+`:65 := sphere_index.add

  notation x <= y := sphere_index.leq x y
  notation x ≤ y := sphere_index.leq x y

  definition succ_le_succ {n m : sphere_index} (H : n ≤ m) : n.+1 ≤ m.+1 := H
  definition le_of_succ_le_succ {n m : sphere_index} (H : n.+1 ≤ m.+1) : n ≤ m := H
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
| n.+1 := suspension (sphere n)

namespace sphere

  definition base {n : ℕ} : sphere n := !north
  definition pointed_sphere [instance] [constructor] (n : ℕ) : pointed (sphere n) :=
  pointed.mk base
  definition Sphere [constructor] (n : ℕ) : Pointed := pointed.mk' (sphere n)

  namespace ops
  abbreviation S := sphere
  notation `S.` := Sphere
  end ops
  open sphere.ops

  definition bool_of_sphere [reducible] : S 0 → bool :=
  suspension.rec ff tt (λx, empty.elim x)

  definition sphere_of_bool [reducible] : bool → S 0
  | ff := !north
  | tt := !south

  definition sphere_equiv_bool : S 0 ≃ bool :=
  equiv.MK bool_of_sphere
           sphere_of_bool
           (λb, match b with | tt := idp | ff := idp end)
           (λx, suspension.rec_on x idp idp (empty.rec _))

  definition sphere_eq_bool : S 0 = bool :=
  ua sphere_equiv_bool

  definition sphere_eq_bool_pointed : S. 0 = Bool :=
  Pointed_eq sphere_equiv_bool idp

  definition pointed_map_sphere (A : Pointed) (n : ℕ) : map₊ (S. n) A ≃ Ω[n] A :=
  begin
    revert A, induction n with n IH,
    { intro A, rewrite [sphere_eq_bool_pointed], apply pointed_map_bool_equiv},
    { intro A, transitivity _, apply suspension_adjoint_loop (S. n) A, apply IH}
  end

end sphere

open sphere sphere.ops

structure weakly_constant [class] {A B : Type} (f : A → B) := --move
  (is_constant : Πa a', f a = f a')

namespace trunc
  open trunc_index
  definition is_trunc_of_pointed_map_sphere_constant (n : ℕ) (A : Type)
    (H : Π(a : A) (f : map₊ (S. n) (pointed.Mk a)) (x : S n), f x = f base) : is_trunc (n.-2.+1) A :=
  begin
    apply iff.elim_right !is_trunc_iff_is_contr_loop,
    intro a,
    apply is_trunc_equiv_closed, apply pointed_map_sphere,
    fapply is_contr.mk,
    { exact pointed_map.mk (λx, a) idp},
    { intro f, fapply pointed_map_eq,
      { intro x, esimp, refine !respect_pt⁻¹ ⬝ (!H ⬝ !H⁻¹)},
      { rewrite [▸*,con.right_inv,▸*,con.left_inv]}}
  end


  definition is_trunc_iff_map_sphere_constant (n : ℕ) (A : Type)
    (H : Π(f : S n → A) (x : S n), f x = f base) : is_trunc (n.-2.+1) A :=
  begin
    apply is_trunc_of_pointed_map_sphere_constant,
    intros, cases f with f p, esimp at *, apply H
  end

end trunc

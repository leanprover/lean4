/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.circle
Authors: Floris van Doorn

Declaration of the n-spheres
-/

import .suspension

open eq nat suspension bool is_trunc unit

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
  nat.rec_on n (-1.+1) (λ n k, k.+1)

  definition trunc_index_of_sphere_index [coercion] [reducible] (n : sphere_index) : trunc_index :=
  sphere_index.rec_on n -1 (λ n k, k.+1)

end sphere_index

open sphere_index equiv

definition sphere : sphere_index → Type₀
| -1   := empty
| n.+1 := suspension (sphere n)

namespace sphere
  namespace ops
  abbreviation S := sphere
  end ops

  definition bool_of_sphere [reducible] : sphere 0 → bool :=
  suspension.rec tt ff (λx, empty.elim _ x)

  definition sphere_of_bool [reducible] : bool → sphere 0
  | tt := !north
  | ff := !south

  definition sphere_equiv_bool : sphere 0 ≃ bool :=
  equiv.MK bool_of_sphere
           sphere_of_bool
           (λb, match b with | tt := idp | ff := idp end)
           (λx, suspension.rec_on x idp idp (empty.rec _))

end sphere

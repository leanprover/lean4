/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

truncating an ∞-group to a group
-/

import hit.trunc algebra.group

open eq is_trunc trunc

namespace algebra

  section
  parameters (A : Type) (mul : A → A → A) (inv : A → A) (one : A)
    {mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c)}
    {one_mul : ∀a, mul one a = a} {mul_one : ∀a, mul a one = a}
    {mul_left_inv : ∀a, mul (inv a) a = one}

  local abbreviation G := trunc 0 A

  include mul_assoc one_mul mul_one mul_left_inv
  definition trunc_mul [unfold 9 10] (g h : G) : G :=
  begin
    apply trunc.rec_on g, intro p,
    apply trunc.rec_on h, intro q,
    exact tr (mul p q)
  end

  definition trunc_inv [unfold 9] (g : G) : G :=
  begin
    apply trunc.rec_on g, intro p,
    exact tr (inv p)
  end

  definition trunc_one [constructor] : G :=
  tr one

  local notation 1 := trunc_one
  local postfix ⁻¹ := trunc_inv
  local infix * := trunc_mul

  theorem trunc_mul_assoc (g₁ g₂ g₃ : G) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    apply trunc.rec_on g₁, intro p₁,
    apply trunc.rec_on g₂, intro p₂,
    apply trunc.rec_on g₃, intro p₃,
    exact ap tr !mul_assoc,
  end

  theorem trunc_one_mul (g : G) : 1 * g = g :=
  begin
    apply trunc.rec_on g, intro p,
    exact ap tr !one_mul
  end

  theorem trunc_mul_one (g : G) : g * 1 = g :=
  begin
    apply trunc.rec_on g, intro p,
    exact ap tr !mul_one
  end

  theorem trunc_mul_left_inv (g : G) : g⁻¹ * g = 1 :=
  begin
    apply trunc.rec_on g, intro p,
    exact ap tr !mul_left_inv
  end

  theorem trunc_mul_comm (mul_comm : ∀a b, mul a b = mul b a) (g h : G)
    : g * h = h * g :=
  begin
    apply trunc.rec_on g, intro p,
    apply trunc.rec_on h, intro q,
    exact ap tr !mul_comm
  end

  parameters (mul_assoc) (one_mul) (mul_one) (mul_left_inv) {A}

  definition trunc_group [constructor] : group G :=
  ⦃group,
    mul          := trunc_mul,
    mul_assoc    := trunc_mul_assoc,
    one          := trunc_one,
    one_mul      := trunc_one_mul,
    mul_one      := trunc_mul_one,
    inv          := trunc_inv,
    mul_left_inv := trunc_mul_left_inv,
   is_set_carrier := _⦄


  definition trunc_comm_group [constructor] (mul_comm : ∀a b, mul a b = mul b a) : comm_group G :=
  ⦃comm_group, trunc_group, mul_comm := trunc_mul_comm mul_comm⦄

  end
end algebra

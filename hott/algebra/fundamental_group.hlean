/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

fundamental group of a pointed space
-/

import hit.trunc algebra.group types.pointed

open core eq trunc algebra is_trunc pointed

namespace fundamental_group
  section
  parameters {A : Type} (a : A)
  definition carrier [reducible] : Type :=
  trunc 0 (a = a)

  local abbreviation G := carrier

  definition mul (g h : G) : G :=
  begin
    apply trunc.rec_on g, intro p,
    apply trunc.rec_on h, intro q,
    exact tr (p ⬝ q)
  end

  definition inv (g : G) : G :=
  begin
    apply trunc.rec_on g, intro p,
    exact tr p⁻¹
  end

  definition one : G :=
  tr idp

  local notation 1 := one
  local postfix ⁻¹ := inv
  local infix * := mul

  definition mul_assoc (g₁ g₂ g₃ : G) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    apply trunc.rec_on g₁, intro p₁,
    apply trunc.rec_on g₂, intro p₂,
    apply trunc.rec_on g₃, intro p₃,
    exact ap tr !con.assoc,
  end

  definition one_mul (g : G) : 1 * g = g :=
  begin
    apply trunc.rec_on g, intro p,
    exact ap tr !idp_con,
  end

  definition mul_one (g : G) : g * 1 = g :=
  begin
    apply trunc.rec_on g, intro p,
    exact idp,
  end

  definition mul_left_inv (g : G) : g⁻¹ * g = 1 :=
  begin
    apply trunc.rec_on g, intro p,
    apply ap tr !con.left_inv
  end

  definition group : group G :=
  ⦃group,
    mul          := mul,
    mul_assoc    := mul_assoc,
    one          := one,
    one_mul      := one_mul,
    mul_one      := mul_one,
    inv          := inv,
    mul_left_inv := mul_left_inv,
   is_hset_carrier := _⦄

  end
end fundamental_group
attribute fundamental_group.group [instance] [constructor] [priority 800]

definition fundamental_group [constructor] (A : Type) [H : pointed A]: Group :=
Group.mk (fundamental_group.carrier (point A)) _

namespace core
  prefix `π₁`:95 := fundamental_group
end core

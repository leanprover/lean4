/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

General properties of binary operations.
-/
open function

namespace binary
  section
    variable {A : Type}
    variables (op₁ : A → A → A) (inv : A → A) (one : A)

    local notation a * b := op₁ a b
    local notation a ⁻¹  := inv a

    attribute [reducible]
    definition commutative := ∀a b, a * b = b * a
    attribute [reducible]
    definition associative := ∀a b c, (a * b) * c = a * (b * c)
    attribute [reducible]
    definition left_identity := ∀a, one * a = a
    attribute [reducible]
    definition right_identity := ∀a, a * one = a
    attribute [reducible]
    definition left_inverse := ∀a, a⁻¹ * a = one
    attribute [reducible]
    definition right_inverse := ∀a, a * a⁻¹ = one
    attribute [reducible]
    definition left_cancelative := ∀a b c, a * b = a * c → b = c
    attribute [reducible]
    definition right_cancelative := ∀a b c, a * b = c * b → a = c

    attribute [reducible]
    definition inv_op_cancel_left := ∀a b, a⁻¹ * (a * b) = b
    attribute [reducible]
    definition op_inv_cancel_left := ∀a b, a * (a⁻¹ * b) = b
    attribute [reducible]
    definition inv_op_cancel_right := ∀a b, a * b⁻¹ * b =  a
    attribute [reducible]
    definition op_inv_cancel_right := ∀a b, a * b * b⁻¹ = a

    variable (op₂ : A → A → A)

    local notation a + b := op₂ a b

    attribute [reducible]
    definition left_distributive := ∀a b c, a * (b + c) = a * b + a * c
    attribute [reducible]
    definition right_distributive := ∀a b c, (a + b) * c = a * c + b * c

    attribute [reducible]
    definition right_commutative {B : Type} (f : B → A → B) := ∀ b a₁ a₂, f (f b a₁) a₂ = f (f b a₂) a₁
    attribute [reducible]
    definition left_commutative {B : Type}  (f : A → B → B) := ∀ a₁ a₂ b, f a₁ (f a₂ b) = f a₂ (f a₁ b)
  end

  section
    variable {A : Type}
    variable {f : A → A → A}
    variable H_comm : commutative f
    variable H_assoc : associative f
    local infixl `*` := f
    include H_comm
    theorem left_comm : left_commutative f :=
    take a b c, calc
      a*(b*c) = (a*b)*c  : eq.symm (H_assoc _ _ _)
        ...   = (b*a)*c  : sorry -- by rewrite (H_comm a b)
        ...   = b*(a*c)  : H_assoc _ _ _

    theorem right_comm : right_commutative f :=
    take a b c, calc
      (a*b)*c = a*(b*c) : H_assoc _ _ _
        ...   = a*(c*b) : sorry -- by rewrite (H_comm b c)
        ...   = (a*c)*b : eq.symm (H_assoc _ _ _)

    theorem comm4 (a b c d : A) : a*b*(c*d) = a*c*(b*d) :=
    calc
      a*b*(c*d) = a*b*c*d   : eq.symm (H_assoc _ _ _)
        ...     = a*c*b*d   : sorry -- by rewrite (right_comm H_comm H_assoc a b c)
        ...     = a*c*(b*d) : H_assoc _ _ _
  end

  section
    variable {A : Type}
    variable {f : A → A → A}
    variable H_assoc : associative f
    local infixl `*` := f
    theorem assoc4helper (a b c d) : (a*b)*(c*d) = a*((b*c)*d) :=
    calc
      (a*b)*(c*d) = a*(b*(c*d)) : H_assoc _ _ _
              ... = a*((b*c)*d) : sorry -- by rewrite (H_assoc b c d)
  end

  attribute [reducible]
  definition right_commutative_comp_right
    {A B : Type} (f : A → A → A) (g : B → A) (rcomm : right_commutative f) : right_commutative (comp_right f g) :=
  λ a b₁ b₂, rcomm _ _ _

  attribute [reducible]
  definition left_commutative_compose_left
    {A B : Type} (f : A → A → A) (g : B → A) (lcomm : left_commutative f) : left_commutative (comp_left f g) :=
  λ a b₁ b₂, lcomm _ _ _
end binary

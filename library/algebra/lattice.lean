/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import .order

variable {A : Type}

/- lattices (we could split this to upper- and lower-semilattices, if needed) -/

structure lattice [class] (A : Type) extends weak_order A :=
(inf : A → A → A)
(sup : A → A → A)
(inf_le_left : ∀ a b, le (inf a b) a)
(inf_le_right : ∀ a b, le (inf a b) b)
(le_inf : ∀a b c, le c a → le c b → le c (inf a b))
(le_sup_left : ∀ a b, le a (sup a b))
(le_sup_right : ∀ a b, le b (sup a b))
(sup_le : ∀ a b c, le a c → le b c → le (sup a b) c)

definition inf := @lattice.inf
definition sup := @lattice.sup
infix ` ⊓ `:70 := inf
infix ` ⊔ `:65 := sup

section
  variable [s : lattice A]
  include s

  theorem inf_le_left (a b : A) : a ⊓ b ≤ a := !lattice.inf_le_left

  theorem inf_le_right (a b : A) : a ⊓ b ≤ b := !lattice.inf_le_right

  theorem le_inf {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ a ⊓ b := !lattice.le_inf H₁ H₂

  theorem le_sup_left (a b : A) : a ≤ a ⊔ b := !lattice.le_sup_left

  theorem le_sup_right (a b : A) : b ≤ a ⊔ b := !lattice.le_sup_right

  theorem sup_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : a ⊔ b ≤ c := !lattice.sup_le H₁ H₂

  /- inf -/

  theorem eq_inf {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :
    c = a ⊓ b :=
  le.antisymm (le_inf H₁ H₂) (H₃ !inf_le_left !inf_le_right)

  theorem inf.comm (a b : A) : a ⊓ b = b ⊓ a :=
  eq_inf !inf_le_right !inf_le_left (λ c H₁ H₂, le_inf H₂ H₁)

  theorem inf.assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  begin
    apply eq_inf,
    { apply le.trans, apply inf_le_left, apply inf_le_left },
    { apply le_inf, apply le.trans, apply inf_le_left, apply inf_le_right, apply inf_le_right },
    { intros [d, H₁, H₂], apply le_inf, apply le_inf H₁, apply le.trans H₂, apply inf_le_left,
      apply le.trans H₂, apply inf_le_right }
  end

  theorem inf.left_comm (a b c : A) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) :=
  binary.left_comm (@inf.comm A s) (@inf.assoc A s) a b c

  theorem inf.right_comm (a b c : A) : (a ⊓ b) ⊓ c = (a ⊓ c) ⊓ b :=
  binary.right_comm (@inf.comm A s) (@inf.assoc A s) a b c

  theorem inf_self (a : A) : a ⊓ a = a :=
  by apply eq.symm; apply eq_inf (le.refl a) !le.refl; intros; assumption

  theorem inf_eq_left {a b : A} (H : a ≤ b) : a ⊓ b = a :=
  by apply eq.symm; apply eq_inf !le.refl H; intros; assumption

  theorem inf_eq_right {a b : A} (H : b ≤ a) : a ⊓ b = b :=
  eq.subst !inf.comm (inf_eq_left H)

  /- sup -/

  theorem eq_sup {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = a ⊔ b :=
  le.antisymm (H₃ !le_sup_left !le_sup_right) (sup_le H₁ H₂)

  theorem sup.comm (a b : A) : a ⊔ b = b ⊔ a :=
  eq_sup !le_sup_right !le_sup_left (λ c H₁ H₂, sup_le H₂ H₁)

  theorem sup.assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
  begin
    apply eq_sup,
    { apply le.trans, apply le_sup_left a b, apply le_sup_left },
    { apply sup_le, apply le.trans, apply le_sup_right a b, apply le_sup_left, apply le_sup_right },
    { intros [d, H₁, H₂], apply sup_le, apply sup_le H₁, apply le.trans !le_sup_left H₂,
      apply le.trans !le_sup_right H₂}
  end

  theorem sup.left_comm (a b c : A) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) :=
  binary.left_comm (@sup.comm A s) (@sup.assoc A s) a b c

  theorem sup.right_comm (a b c : A) : (a ⊔ b) ⊔ c = (a ⊔ c) ⊔ b :=
  binary.right_comm (@sup.comm A s) (@sup.assoc A s) a b c

  theorem sup_self (a : A) : a ⊔ a = a :=
  by apply eq.symm; apply eq_sup (le.refl a) !le.refl; intros; assumption

  theorem sup_eq_left {a b : A} (H : b ≤ a) : a ⊔ b = a :=
  by apply eq.symm; apply eq_sup !le.refl H; intros; assumption

  theorem sup_eq_right {a b : A} (H : a ≤ b) : a ⊔ b = b :=
  eq.subst !sup.comm (sup_eq_left H)
end

/- lattice instances  -/

definition lattice_Prop [instance] : lattice Prop :=
⦃ lattice, weak_order_Prop,
  inf          := and,
  le_inf       := take a b c Ha Hb Hc, and.intro (Ha Hc) (Hb Hc),
  inf_le_left  := @and.elim_left,
  inf_le_right := @and.elim_right,
  sup          := or,
  sup_le       := @or.rec,
  le_sup_left  := @or.intro_left,
  le_sup_right := @or.intro_right
⦄

definition lattice_fun [instance] {A B : Type} [lattice B] : lattice (A → B) :=
⦃ lattice, weak_order_fun,
  inf          := λf g x, inf (f x) (g x),
  le_inf       := take f g h Hf Hg x, le_inf (Hf x) (Hg x),
  inf_le_left  := take f g x, !inf_le_left,
  inf_le_right := take f g x, !inf_le_right,
  sup          := λf g x, sup (f x) (g x),
  sup_le       := take f g h Hf Hg x, sup_le (Hf x) (Hg x),
  le_sup_left  := take f g x, !le_sup_left,
  le_sup_right := take t g x, !le_sup_right
⦄

/-
  Should we add a trans-instance from total orders to lattices?
  If we added we should add it with lower priority:
    Prop is added as a lattice, but in the classical case it is a total order!
-/

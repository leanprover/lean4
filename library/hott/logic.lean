-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

inductive path {A : Type} (a : A) : A → Type :=
| refl : path a a

infix `=`:50 := path

definition transport {A : Type} {a b : A} {P : A → Type} (H1 : a = b) (H2 : P a) : P b
:= path_rec H2 H1

notation p `*(`:75 u `)` := transport p u

definition symm {A : Type} {a b : A} (p : a = b) : b = a
:= p*(refl a)

definition trans {A : Type} {a b c : A} (p1 : a = b) (p2 : b = c) : a = c
:= p2*(p1)

namespace path_notation
  postfix `⁻¹`:100 := symm
  infixr `⬝`:75 := trans
end
using path_notation

theorem trans_refl_right {A : Type} {x y : A} (p : x = y) : p = p ⬝ (refl y)
:= refl p

theorem trans_refl_left {A : Type} {x y : A} (p : x = y) : p = (refl x) ⬝ p
:= path_rec (trans_refl_right (refl x)) p

theorem refl_symm {A : Type} (x : A) : (refl x)⁻¹ = (refl x)
:= refl (refl x)

theorem refl_trans {A : Type} (x : A) : (refl x) ⬝ (refl x) = (refl x)
:= refl (refl x)

theorem trans_symm {A : Type} {x y : A} (p : x = y) : p ⬝ p⁻¹ = refl x
:= have q : (refl x) ⬝ (refl x)⁻¹ = refl x, from
     ((refl_symm x)⁻¹)*(refl_trans x),
   path_rec q p

theorem symm_trans {A : Type} {x y : A} (p : x = y) : p⁻¹ ⬝ p = refl y
:= have q : (refl x)⁻¹ ⬝ (refl x) = refl x, from
     ((refl_symm x)⁻¹)*(refl_trans x),
   path_rec q p

theorem symm_symm {A : Type} {x y : A} (p : x = y) : (p⁻¹)⁻¹ = p
:= have q : ((refl x)⁻¹)⁻¹ = refl x, from
     refl (refl x),
   path_rec q p

theorem trans_assoc {A : Type} {x y z w : A} (p : x = y) (q : y = z) (r : z = w) : p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r
:= have e1 : (p ⬝ q) ⬝ (refl z) = p ⬝ q, from
     (trans_refl_right (p ⬝ q))⁻¹,
   have e2 : q ⬝ (refl z) = q, from
     (trans_refl_right q)⁻¹,
   have e3 : p ⬝ (q ⬝ (refl z)) = p ⬝ q, from
     e2*(refl (p ⬝ (q ⬝ (refl z)))),
   path_rec (e3 ⬝ e1⁻¹) r

theorem ap {A : Type} {B : Type} (f : A → B) {a b : A} (p : a = b) : f a = f b
:= p*(refl (f a))

section
  parameter {A : Type}
  parameter {B : A → Type}
  parameter f : Π x, B x
  definition D [private] (x y : A) (p : x = y) := p*(f x) = f y
  definition d [private] (x : A) : D x x (refl x)
  := refl (f x)
  theorem apd {a b : A} (p : a = b) : p*(f a) = f b
  := path_rec (d a) p
end

definition homotopy {A : Type} {P : A → Type} (f g : Π x, P x)
:= Π x, f x = g x

infix `∼`:50 := homotopy

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

section
  parameter {A : Type}
  parameter {B : Type}
  theorem hom_refl (f : A → B) : f ∼ f
  := take x, refl (f x)
  theorem hom_symm {f g : A → B} : f ∼ g → g ∼ f
  := assume h, take x, (h x)⁻¹
  theorem hom_trans {f g h : A → B} : f ∼ g → g ∼ h → f ∼ h
  := assume h1 h2, take x, (h1 x) ⬝ (h2 x)
end

inductive empty : Type :=
-- empty

theorem empty_elim (c : Type) (H : empty) : c
:= empty_rec (λ e, c) H

definition not (A : Type) := A → empty
prefix `¬`:40 := not

theorem not_intro {a : Type} (H : a → empty) : ¬ a
:= H

theorem not_elim {a : Type} (H1 : ¬ a) (H2 : a) : empty
:= H1 H2

theorem absurd {a : Type} (H1 : a) (H2 : ¬ a) : empty
:= H2 H1

theorem mt {a b : Type} (H1 : a → b) (H2 : ¬ b) : ¬ a
:= assume Ha : a, absurd (H1 Ha) H2

theorem contrapos {a b : Type} (H : a → b) : ¬ b → ¬ a
:= assume Hnb : ¬ b, mt H Hnb

theorem absurd_elim {a : Type} (b : Type) (H1 : a) (H2 : ¬ a) : b
:= empty_elim b (absurd H1 H2)

inductive unit : Type :=
| star : unit

notation `⋆`:max := star

theorem absurd_not_unit (H : ¬ unit) : empty
:= absurd star H

theorem not_empty_trivial : ¬ empty
:= assume H : empty, H

theorem upun (x : unit) : x = ⋆
:= unit_rec (refl ⋆) x

inductive product (A : Type) (B : Type) : Type :=
| pair : A → B → product A B

infixr `∧`:30 := product

notation `(` h `,` t:(foldl `,` (e r, pair r e) h) `)` := t

definition pr1 {A : Type} {B : Type} (p : A ∧ B) : A
:= product_rec (λ a b, a) p

definition pr2 {A : Type} {B : Type} (p : A ∧ B) : B
:= product_rec (λ a b, b) p

theorem uppt {A : Type} {B : Type} (p : A ∧ B) : (pr1 p, pr2 p) = p
:= product_rec (λ x y, refl (x, y)) p

inductive sum (A : Type) (B : Type) : Type :=
| inl : A → sum A B
| inr : B → sum A B

infixr `∨`:25 := sum

theorem sum_elim {a : Type} {b : Type} {c : Type} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= sum_rec H2 H3 H1

theorem resolve_right {a : Type} {b : Type} (H1 : a ∨ b) (H2 : ¬ a) : b
:= sum_elim H1 (assume Ha, absurd_elim b Ha H2) (assume Hb, Hb)

theorem resolve_left {a : Type} {b : Type} (H1 : a ∨ b) (H2 : ¬ b) : a
:= sum_elim H1 (assume Ha, Ha) (assume Hb, absurd_elim a Hb H2)

theorem or_flip {a : Type} {b : Type} (H : a ∨ b) : b ∨ a
:= sum_elim H (assume Ha, inr b Ha) (assume Hb, inl a Hb)

inductive bool : Type :=
| true  : bool
| false : bool

theorem bool_cases (p : bool) : p = true ∨ p = false
:= bool_rec (inl _ (refl true)) (inr _ (refl false)) p

inductive Sigma {A : Type} (B : A → Type) : Type :=
| sigma : Π a, B a → Sigma B

notation `Σ` binders `,` r:(scoped P, Sigma P) := r

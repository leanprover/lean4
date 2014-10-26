import logic data.prod
open eq.ops prod tactic

inductive tree (A : Type) :=
leaf : A → tree A,
node : tree A → tree A → tree A

inductive one.{l} : Type.{max 1 l} :=
star : one

set_option pp.universes true

namespace tree
  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable (C : tree A → Type.{l₂})
    definition below (t : tree A) : Type :=
    rec_on t (λ a, one.{l₂}) (λ t₁ t₂ r₁ r₂, C t₁ × C t₂ × r₁ × r₂)
  end

  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : tree A → Type.{l₂}}
    definition below_rec_on (t : tree A) (H : Π (n : tree A), below C n → C n) : C t
    := have general : C t × below C t, from
        rec_on t
          (λa, (H (leaf a) one.star, one.star))
          (λ (l r : tree A) (Hl : C l × below C l) (Hr : C r × below C r),
            have b : below C (node l r), from
              (pr₁ Hl, pr₁ Hr, pr₂ Hl, pr₂ Hr),
            have c : C (node l r), from
              H (node l r) b,
            (c, b)),
       pr₁ general
  end

  definition no_confusion_type {A : Type} (P : Type) (t₁ t₂ : tree A) : Type :=
  cases_on t₁
   (λ a₁, cases_on t₂
     (λ a₂,    (a₁ = a₂ → P) → P)
     (λ l₂ r₂, P))
   (λ l₁ r₁, cases_on t₂
     (λ a₂,    P)
     (λ l₂ r₂, (l₁ = l₂ → r₁ = r₂ → P) → P))

  set_option pp.universes true
  check no_confusion_type

  definition no_confusion {A : Type} {P : Type} {t₁ t₂ : tree A} : t₁ = t₂ → no_confusion_type P t₁ t₂ :=
  assume e₁ : t₁ = t₂,
    have aux₁ : t₁ = t₁ → no_confusion_type P t₁ t₁, from
      take h, cases_on t₁
        (λ a,   assume h : a = a → P, h (eq.refl a))
        (λ l r, assume h : l = l → r = r → P, h (eq.refl l) (eq.refl r)),
    eq.rec aux₁ e₁ e₁

  check no_confusion

  theorem leaf_ne_tree {A : Type} (a : A) (l r : tree A) : leaf a ≠ node l r :=
  assume h : leaf a = node l r,
  no_confusion h

  constant A : Type₁
  constants l₁ l₂ r₁ r₂ : tree A
  axiom node_eq : node l₁ r₁ = node l₂ r₂
  check no_confusion node_eq

  definition tst : (l₁ = l₂ → r₁ = r₂ → l₁ = l₂) → l₁ = l₂ := no_confusion node_eq
  check tst (λ e₁ e₂, e₁)

  theorem node.inj1 {A : Type} (l₁ l₂ r₁ r₂ : tree A) : node l₁ r₁ = node l₂ r₂ → l₁ = l₂ :=
  assume h,
    have trivial : (l₁ = l₂ → r₁ = r₂ → l₁ = l₂) → l₁ = l₂, from no_confusion h,
    trivial (λ e₁ e₂, e₁)

  theorem node.inj2 {A : Type} (l₁ l₂ r₁ r₂ : tree A) : node l₁ r₁ = node l₂ r₂ → l₁ = l₂ :=
  begin
    intro h,
    apply (no_confusion h),
    intros, assumption
  end

  theorem node.inj3 {A : Type} {l₁ l₂ r₁ r₂ : tree A} (h : node l₁ r₁ = node l₂ r₂) : l₁ = l₂ :=
  begin
    apply (no_confusion h),
    assume (e₁ : l₁ = l₂) (e₂ : r₁ = r₂), e₁
  end

  theorem node.inj4 {A : Type} {l₁ l₂ r₁ r₂ : tree A} (h : node l₁ r₁ = node l₂ r₂) : l₁ = l₂ :=
  begin
    apply (no_confusion h),
    assume e₁ e₂, e₁
  end

end tree

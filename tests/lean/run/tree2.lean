import logic data.prod
open eq.ops prod tactic

inductive tree (A : Type) :=
| leaf : A → tree A
| node : tree A → tree A → tree A

inductive one1.{l} : Type.{max 1 l} :=
star : one1

set_option pp.universes true

namespace tree
  namespace manual
  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable (C : tree A → Type.{l₂})
    definition below (t : tree A) : Type :=
    tree.rec_on t (λ a, one1.{l₂}) (λ t₁ t₂ r₁ r₂, C t₁ × C t₂ × r₁ × r₂)
  end

  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : tree A → Type.{l₂}}
    definition below_rec_on (t : tree A) (H : Π (n : tree A), below C n → C n) : C t
    := have general : C t × below C t, from
        tree.rec_on t
          (λa, (H (leaf a) one1.star, one1.star))
          (λ (l r : tree A) (Hl : C l × below C l) (Hr : C r × below C r),
            have b : below C (node l r), from
              (pr₁ Hl, pr₁ Hr, pr₂ Hl, pr₂ Hr),
            have c : C (node l r), from
              H (node l r) b,
            (c, b)),
       pr₁ general
  end
  end manual

  check tree.no_confusion

  theorem leaf_ne_tree {A : Type} (a : A) (l r : tree A) : leaf a ≠ node l r :=
  assume h : leaf a = node l r,
  tree.no_confusion h

  constant A : Type₁
  constants l₁ l₂ r₁ r₂ : tree A
  axiom node_eq : node l₁ r₁ = node l₂ r₂
  check tree.no_confusion node_eq

  definition tst : (l₁ = l₂ → r₁ = r₂ → l₁ = l₂) → l₁ = l₂ := tree.no_confusion node_eq
  check tst (λ e₁ e₂, e₁)

  theorem node.inj1 {A : Type} (l₁ l₂ r₁ r₂ : tree A) : node l₁ r₁ = node l₂ r₂ → l₁ = l₂ :=
  assume h,
    have trivial : (l₁ = l₂ → r₁ = r₂ → l₁ = l₂) → l₁ = l₂, from tree.no_confusion h,
    trivial (λ e₁ e₂, e₁)

  theorem node.inj2 {A : Type} (l₁ l₂ r₁ r₂ : tree A) : node l₁ r₁ = node l₂ r₂ → l₁ = l₂ :=
  begin
    intro h,
    apply (tree.no_confusion h),
    intros, assumption
  end
end tree

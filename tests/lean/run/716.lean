private def eqv (p₁ p₂ : α × α) : Prop :=
 (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv

axiom eqv.refl {α} (p : α × α) : p ~ p

axiom eqv.symm  {α} : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁

axiom eqv.trans {α} : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance uprodSetoid (α : Type u) : Setoid (α × α) where
   r     := eqv
   iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

@[noinline] def myId := @id

def mk' {α : Type} : α × α → UProd α :=
  let f := @Quot.mk _ _
  myId f

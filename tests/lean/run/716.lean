private def Eqv (p₁ p₂ : α × α) : Prop :=
 (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => Eqv

axiom Eqv.refl {α} (p : α × α) : p ~ p

axiom Eqv.symm  {α} : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁

axiom Eqv.trans {α} : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃

private theorem is_equivalence : Equivalence (@Eqv α) :=
  { refl := Eqv.refl, symm := Eqv.symm, trans := Eqv.trans }

instance uprodSetoid (α : Type u) : Setoid (α × α) where
   R      := Eqv
   is_eqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

@[noinline] def myId := @id

def mk' {α : Type} : α × α → UProd α :=
  let f := @Quot.mk _ _
  myId f

section Mathlib.Init.Order.Defs

universe u
variable {α : Type u}

class Preorder (α : Type u) extends LE α, LT α

theorem le_trans [Preorder α] : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c := sorry

class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

end Mathlib.Init.Order.Defs

section Mathlib.Init.Set

set_option autoImplicit true

def Set (α : Type u) := α → Prop

namespace Set

protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

def image (f : α → β) (s : Set α) : Set β := fun b => ∃ a, ∃ (_ : a ∈ s), f a = b

end Set

end Mathlib.Init.Set

section Mathlib.Data.Subtype

attribute [coe] Subtype.val

end Mathlib.Data.Subtype

section Mathlib.Order.Notation

class Sup (α : Type _) where
  sup : α → α → α

class Inf (α : Type _) where
  inf : α → α → α

@[inherit_doc]
infixl:68 " ⊔ " => Sup.sup

@[inherit_doc]
infixl:69 " ⊓ " => Inf.inf

class Top (α : Type _) where
  top : α

class Bot (α : Type _) where
  bot : α

notation "⊤" => Top.top

notation "⊥" => Bot.bot

end Mathlib.Order.Notation

section Mathlib.Data.Set.Defs

universe u

namespace Set

variable {α : Type u}

@[coe, reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

end Set

end Mathlib.Data.Set.Defs

section Mathlib.Order.Basic

universe u

variable {α : Type u}

def Preorder.lift {α β} [Preorder β] (f : α → β) : Preorder α where
  le x y := f x ≤ f y
  lt x y := f x < f y

def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) : PartialOrder α :=
  { Preorder.lift f with le_antisymm := sorry }

namespace Subtype

instance le [LE α] {p : α → Prop} : LE (Subtype p) :=
  ⟨fun x y ↦ (x : α) ≤ y⟩

instance lt [LT α] {p : α → Prop} : LT (Subtype p) :=
  ⟨fun x y ↦ (x : α) < y⟩

instance partialOrder [PartialOrder α] (p : α → Prop) : PartialOrder (Subtype p) :=
  PartialOrder.lift (fun (a : Subtype p) ↦ (a : α))

end Subtype

end Mathlib.Order.Basic

section Mathlib.Order.Lattice

universe u
variable {α : Type u}

class SemilatticeSup (α : Type u) extends Sup α, PartialOrder α where
  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

theorem sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c := sorry

end SemilatticeSup

class SemilatticeInf (α : Type u) extends Inf α, PartialOrder α where
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

section SemilatticeInf

variable [SemilatticeInf α] {a b c d : α}

theorem inf_le_left : a ⊓ b ≤ a := sorry

theorem le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c := sorry

end SemilatticeInf

class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

namespace Subtype

protected def semilatticeSup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } where
  sup x y := ⟨x.1 ⊔ y.1, sorry⟩
  le_sup_left _ _ := sorry
  le_sup_right _ _ := sorry
  sup_le _ _ _ h1 h2 := sorry

protected def semilatticeInf [SemilatticeInf α] {P : α → Prop}
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    SemilatticeInf { x : α // P x } where
  inf x y := ⟨x.1 ⊓ y.1, sorry⟩
  inf_le_left _ _ := sorry
  inf_le_right _ _ := sorry
  le_inf _ _ _ h1 h2 := sorry

end Subtype


end Mathlib.Order.Lattice

section Mathlib.Order.BoundedOrder

universe u

class OrderTop (α : Type u) [LE α] extends Top α where
  le_top : ∀ a : α, a ≤ ⊤

class OrderBot (α : Type u) [LE α] extends Bot α where
  bot_le : ∀ a : α, ⊥ ≤ a

end Mathlib.Order.BoundedOrder

section Mathlib.Data.Set.Intervals.Basic

variable {α : Type _} [Preorder α]

def Set.Iic (b : α) : Set α := fun x => x ≤ b

end Mathlib.Data.Set.Intervals.Basic

section Mathlib.Order.SetNotation

universe u
variable {α : Type u}

class SupSet (α : Type _) where
  sSup : Set α → α

class InfSet (α : Type _) where
  sInf : Set α → α

export SupSet (sSup)

export InfSet (sInf)

end Mathlib.Order.SetNotation

section Mathlib.Order.CompleteLattice

variable {α : Type _}

class CompleteSemilatticeSup (α : Type _) extends PartialOrder α, SupSet α where
  sSup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → sSup s ≤ a

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

theorem sSup_le : (∀ b ∈ s, b ≤ a) → sSup s ≤ a := sorry
end

class CompleteSemilatticeInf (α : Type _) extends PartialOrder α, InfSet α where
  le_sInf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ sInf s

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

theorem le_sInf : (∀ b ∈ s, a ≤ b) → a ≤ sInf s := sorry

end

class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α,
  CompleteSemilatticeInf α, Top α, Bot α where
  protected le_top : ∀ x : α, x ≤ ⊤
  protected bot_le : ∀ x : α, ⊥ ≤ x

instance (priority := 100) CompleteLattice.toOrderTop [h : CompleteLattice α] : OrderTop α :=
  { h with }
instance (priority := 100) CompleteLattice.toOrderBot [h : CompleteLattice α] : OrderBot α :=
  { h with }

end Mathlib.Order.CompleteLattice

section Mathlib.Order.LatticeIntervals

variable {α : Type _}

namespace Set

namespace Iic

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

instance [Lattice α] {a : α} : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }

instance orderTop [Preorder α] {a : α} : OrderTop (Iic a) := sorry

instance orderBot [Preorder α] [OrderBot α] {a : α} : OrderBot (Iic a) := sorry

end Iic

end Set

end Mathlib.Order.LatticeIntervals

section Mathlib.Order.CompleteLatticeIntervals

variable {α : Type _}

namespace Set.Iic

variable [CompleteLattice α] {a : α}

def instCompleteLattice : CompleteLattice (Iic a) where
  sSup S := ⟨sSup (Set.image (fun x : Iic a => (x : α)) S), sorry⟩
  sInf S := ⟨a ⊓ sInf (Set.image (fun x : Iic a => (x : α)) S), sorry⟩
  sSup_le S b hb := sSup_le <| fun c' ⟨c, hc, hc'⟩ ↦ hc' ▸ hb c hc
  le_sInf S b hb := le_inf_iff.mpr
    ⟨b.property, le_sInf fun d' ⟨d, hd, hd'⟩  ↦ hd' ▸ hb d hd⟩
  le_top := sorry
  bot_le := sorry

example : CompleteLattice (Iic a) where
  sSup S := ⟨sSup (Set.image (fun x : Iic a => (x : α)) S), sorry⟩
  sInf S := ⟨a ⊓ sInf (Set.image (fun x : Iic a => (x : α)) S), sorry⟩
  sSup_le S b hb := sSup_le (α := α) <| fun c' ⟨c, hc, hc'⟩ ↦ hc' ▸ hb c hc
  le_sInf S b hb := (le_inf_iff (α := α)).mpr
    ⟨b.property, le_sInf fun d' ⟨d, hd, hd'⟩  ↦ hd' ▸ hb d hd⟩
  le_top := sorry
  bot_le := sorry

  end Set.Iic

  end Mathlib.Order.CompleteLatticeIntervals

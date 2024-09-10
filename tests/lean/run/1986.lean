instance {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] : LE (∀ i, α i) where
  le x y := ∀ i, x i ≤ y i

class Top (α : Type u) where
  top : α

class Bot (α : Type u) where
  bot : α

notation "⊤" => Top.top

notation "⊥" => Bot.bot

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := λ a b => a ≤ b ∧ ¬ b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)

class PartialOrder (α : Type u) extends Preorder α :=
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
p

namespace Set

protected def Mem (s : Set α) (a : α) : Prop :=
s a

instance : Membership α (Set α) :=
⟨Set.Mem⟩

def range (f : ι → α) : Set α :=
  setOf (λ x => ∃ y, f y = x)

end Set

class InfSet (α : Type _) where
  infₛ : Set α → α

class SupSet (α : Type _) where
  supₛ : Set α → α

export SupSet (supₛ)

export InfSet (infₛ)

open Set

def supᵢ {α : Type _} [SupSet α] {ι} (s : ι → α) : α :=
  supₛ (range s)

def infᵢ {α : Type _} [InfSet α] {ι} (s : ι → α) : α :=
  infₛ (range s)

class HasSup (α : Type u) where
  sup : α → α → α

class HasInf (α : Type u) where
  inf : α → α → α

@[inherit_doc]
infixl:68 " ⊔ " => HasSup.sup

@[inherit_doc]
infixl:69 " ⊓ " => HasInf.inf

class SemilatticeSup (α : Type u) extends HasSup α, PartialOrder α where
  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

class SemilatticeInf (α : Type u) extends HasInf α, PartialOrder α where
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

class CompleteSemilatticeInf (α : Type _) extends PartialOrder α, InfSet α where
  infₛ_le : ∀ s, ∀ a, a ∈ s → infₛ s ≤ a
  le_infₛ : ∀ s a, (∀ b, b ∈ s → a ≤ b) → a ≤ infₛ s

class CompleteSemilatticeSup (α : Type _) extends PartialOrder α, SupSet α where
  le_supₛ : ∀ s, ∀ a, a ∈ s → a ≤ supₛ s
  supₛ_le : ∀ s a, (∀ b, b ∈ s → b ≤ a) → supₛ s ≤ a

class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α,
  CompleteSemilatticeInf α, Top α, Bot α where
  protected le_top : ∀ x : α, x ≤ ⊤
  protected bot_le : ∀ x : α, ⊥ ≤ x

class Frame (α : Type _) extends CompleteLattice α where

class Coframe (α : Type _) extends CompleteLattice α where
  infᵢ_sup_le_sup_infₛ (a : α) (s : Set α) : (infᵢ (λ b => a ⊔ b)) ≤ a ⊔ infₛ s
  -- should be ⨅ b ∈ s but I had problems with notation

class CompleteDistribLattice (α : Type _) extends Frame α where
  infᵢ_sup_le_sup_infₛ : ∀ a s, (infᵢ (λ b => a ⊔ b)) ≤ a ⊔ infₛ s
  -- similarly this is not quite right mathematically but this doesn't matter

-- See note [lower instance priority]
instance (priority := 100) CompleteDistribLattice.toCoframe {α : Type _} [CompleteDistribLattice α] :
    Coframe α :=
  { ‹CompleteDistribLattice α› with }

class OrderTop (α : Type u) [LE α] extends Top α where
  le_top : ∀ a : α, a ≤ ⊤

class OrderBot (α : Type u) [LE α] extends Bot α where
  bot_le : ∀ a : α, ⊥ ≤ a

class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

instance(priority := 100) CompleteLattice.toBoundedOrder  {α : Type _} [h : CompleteLattice α] :
    BoundedOrder α :=
  { h with }

namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance [∀ i, Bot (α' i)] : Bot (∀ i, α' i) :=
  ⟨fun _ => ⊥⟩

instance [∀ i, Top (α' i)] : Top (∀ i, α' i) :=
  ⟨fun _ => ⊤⟩

protected instance LE {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] : LE (∀ i, α i) where
  le x y := ∀ i, x i ≤ y i

instance Preorder {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] : Preorder (∀ i, α i) :=
  { Pi.LE with
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry }

instance PartialOrder {ι : Type u} {α : ι → Type v} [∀ i, PartialOrder (α i)] :
    PartialOrder (∀ i, α i) :=
  { Pi.Preorder with
  le_antisymm := sorry }

instance semilatticeSup [∀ i, SemilatticeSup (α' i)] : SemilatticeSup (∀ i, α' i) where
  le_sup_left _ _ _ := SemilatticeSup.le_sup_left _ _
  le_sup_right _ _ _ := SemilatticeSup.le_sup_right _ _
  sup_le _ _ _ ac bc i := SemilatticeSup.sup_le _ _ _ (ac i) (bc i)

instance semilatticeInf [∀ i, SemilatticeInf (α' i)] : SemilatticeInf (∀ i, α' i) where
  inf_le_left _ _ _ := SemilatticeInf.inf_le_left _ _
  inf_le_right _ _ _ := SemilatticeInf.inf_le_right _ _
  le_inf _ _ _ ac bc i := SemilatticeInf.le_inf _ _ _ (ac i) (bc i)

instance lattice [∀ i, Lattice (α' i)] : Lattice (∀ i, α' i) :=
{ Pi.semilatticeSup, Pi.semilatticeInf with }

instance orderTop [∀ i, LE (α' i)] [∀ i, OrderTop (α' i)] : OrderTop (∀ i, α' i) :=
  { inferInstanceAs (Top (∀ i, α' i)) with le_top := sorry }

instance orderBot [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) :=
  { inferInstanceAs (Bot (∀ i, α' i)) with bot_le := sorry }

instance boundedOrder [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] : BoundedOrder (∀ i, α' i) :=
{ Pi.orderTop, Pi.orderBot with }

instance SupSet {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => supᵢ (λ (f : {f : ∀ i, β i // f ∈ s}) => f.1 i)⟩

instance InfSet {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] : InfSet (∀ i, β i) :=
  ⟨fun s i => infᵢ (λ (f : {f : ∀ i, β i // f ∈ s}) => f.1 i)⟩

instance completeLattice {α : Type _} {β : α → Type _} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) :=
  { Pi.boundedOrder, Pi.lattice with
    le_supₛ := sorry
    infₛ_le := sorry
    supₛ_le := sorry
    le_infₛ := sorry
  }

instance frame {ι : Type _} {π : ι → Type _} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with }

instance coframe {ι : Type _} {π : ι → Type _} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with infᵢ_sup_le_sup_infₛ := sorry }

end Pi

-- very quick (instantaneous) in Lean 4
instance Pi.completeDistribLattice' {ι : Type _} {π : ι → Type _}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) :=
CompleteDistribLattice.mk (Pi.coframe.infᵢ_sup_le_sup_infₛ)

-- User: takes around 2 seconds wall clock time on my PC (but very quick in Lean 3)
set_option maxHeartbeats 400 -- make sure it stays fast
set_option synthInstance.maxHeartbeats 400
instance Pi.completeDistribLattice'' {ι : Type _} {π : ι → Type _}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) :=
  { Pi.frame, Pi.coframe with }
-- quick Lean 3 version:
-- https://github.com/leanprover-community/mathlib/blob/b26e15a46f1a713ce7410e016d50575bb0bc3aa4/src/order/complete_boolean_algebra.lean#L210

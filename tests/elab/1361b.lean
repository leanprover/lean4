def Multiset (α: Type) : Type := sorry
def Multiset.ndinsert [DecidableEq α](a : α): Multiset α → Multiset α := sorry
def Finset (α : Type _) : Type := @Subtype (Multiset α) sorry
def Finset.insert [DecidableEq α](a : α): Finset α → Finset α
| ⟨ms, prop⟩ => ⟨ms.ndinsert a, sorry⟩

inductive Bar : Finset Nat → Type
| insert : Bar (Finset.insert n Γ)
| empty  : Bar Γ

example {Γ: Finset Nat}: ∀  (p: Bar Γ), Nat
| Bar.empty => 1 -- missing cases: (@Bar.insert _ (Subtype.mk _ _))
| _         => 2 -- redundant alternative

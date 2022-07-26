namespace Ex1

inductive Multiset (α: Type): Type
def Finset (α : Type) := @Subtype (Multiset α) (λ _ => True)
def Finset.insert (a : α): Finset α → Finset α := sorry
def Finset.empty : Finset α :=  sorry

structure Foo (G: Fin 0) (m: Nat) where
  n: Nat
  f: Fin m

inductive Bar {G: Fin 0} : {m: Nat} → Finset (Foo G m) → Type where
  | insert : Bar (Finset.insert (Foo.mk n f) Γ)
  | empty : Bar Finset.empty

example {G: Fin 0} : {n: Nat} → {Γ: Finset <| Foo G n} → Bar Γ → Nat
  | Nat.zero,   _, _          => 1
  | Nat.succ _, _, Bar.insert => 2
  | Nat.succ _, _, _          => 3

end Ex1

namespace Ex2

inductive Multiset (α: Type _): Type _
def Finset (α : Type _) := @Subtype (Multiset α) (λ _ => True)
def Finset.insert [DecidableEq α](a : α): Finset α → Finset α := sorry
def Finset.empty : Finset α :=  sorry

structure Foo (G: Fin 0) (m: Nat) where
  n: Nat
  f: Fin m
deriving DecidableEq

inductive Bar {G: Fin 0}: {m: Nat} → Finset (Foo G m) → Type _
| insert: Bar (Finset.insert (Foo.mk n f) Γ)
| empty: Bar Finset.empty

example {G: Fin 0} : ∀ {n: Nat} {Γ: Finset $ Foo G n} (p: Bar Γ), Nat
| 0, _, _ => 0
| _+1, _, Bar.insert  =>  0
| _+1, _, _ => 0

end Ex2

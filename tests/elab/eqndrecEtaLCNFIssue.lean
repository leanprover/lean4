import Lean
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

def ex {G: Fin 0} : {n: Nat} → {Γ: Finset <| Foo G n} → Bar Γ → Nat
  | Nat.zero,   _, _          => 1
  | Nat.succ _, _, Bar.insert => 2
  | Nat.succ _, _, _          => 3

run_meta Lean.Compiler.compile #[``ex]

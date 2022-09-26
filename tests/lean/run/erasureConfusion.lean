import Lean

structure S (α : Type u) (β : Type v) (f : α → β) where
  a : α
  b : β := f a

def f : S Nat Type (fun _ => Nat) :=
 S.mk 0 Nat

#eval Lean.Compiler.compile #[``f]

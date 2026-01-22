structure BoxedProd (α β : Type) where
  fst : α
  snd : β

structure BoxedSigma (α : Type) (β : α → Type) where
  fst : α
  snd : β fst

set_option trace.compiler.ir.reset_reuse true

def f : BoxedProd Nat Nat → BoxedProd Nat Nat
  | ⟨a, b⟩ => ⟨b, a⟩

def Sigma.toProd : BoxedSigma α (fun _ => β) → BoxedProd α β
  | ⟨a, b⟩ => ⟨a, b⟩

def foo : List (Nat × Nat) → List Nat
  | [] => []
  | x :: xs => match x with
      | (a, _) => a :: foo xs

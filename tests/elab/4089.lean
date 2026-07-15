set_option trace.Compiler.resetReuse true

def f : Nat × Nat → Nat × Nat
  | (a, b) => (b, a)

def Sigma.toProd : (_ : α) × β → α × β
  | ⟨a, b⟩ => (a, b)

def foo : List (Nat × Nat) → List Nat
  | [] => []
  | x :: xs => match x with
      | (a, _) => a :: foo xs

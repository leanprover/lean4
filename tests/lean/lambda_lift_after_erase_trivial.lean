structure box (α : Type) :=
(val : α)

set_option trace.compiler.lambda_lifting true

def f1 : box (ℕ → ℕ) :=
box.mk id

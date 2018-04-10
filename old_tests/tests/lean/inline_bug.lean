@[inline] def o (n : ℕ) := prod.mk n n
set_option trace.compiler.inline true
def f := (o 1).fst

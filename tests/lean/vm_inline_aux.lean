namespace ex
set_option trace.compiler.optimize_bytecode true

@[inline] def {u} cond {a : Type u} : bool → a → a → a
| tt x y := x
| ff x y := y

-- cond should be inlined here
def foo (x : bool) :=
100 + cond x (10*10) (20*20)
end ex

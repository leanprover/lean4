import logic

constant fibrant : Type → Prop

structure Fib : Type :=
{type : Type} (pred : fibrant type)

check Fib.mk

constant {u} fibrant : Type u → Prop

structure {u} Fib : Type (u+1) :=
{type : Type u} (pred : fibrant type)

check Fib.mk

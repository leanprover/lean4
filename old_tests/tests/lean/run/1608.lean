example {α : Type} {a b : α} (h : ¬ (a = b)) : b ≠ a :=
by cc

example {α : Type} {a b : α} (h : ¬ (a = b)) : ¬ (b = a) :=
by cc

example {α : Type} {a b : α} (h : ¬ (a = b)) : b ≠ a :=
begin [smt] end

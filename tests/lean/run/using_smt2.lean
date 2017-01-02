open smt_tactic

def ex1 (p q : Prop) : p → q → p :=
by using_smt $ return ()

def ex2 (p q : Prop) : ¬ p → q → ¬ p :=
by using_smt $ return ()

print ex1
print ex2

example (p q : Prop) : p → (p ↔ q) → q :=
by using_smt $ return ()

open nat tactic

example (a b c : Prop) (Ha : a) (Hb : b) (Hc : c) : b :=
by do trace_state, assumption

definition ex1 (a b c : Prop) : a → b → c → b :=
by do intros, assumption

#print ex1

Import tactic.

Variables a b c d e : Bool.
Axiom H1 : a => b.
Axiom H2 : b = c.
Axiom H3 : c => d.
Axiom H4 : d <=> e.

Theorem T : a => e
:= calc a  =>  b : H1
      ...  =   c : H2
      ...  =>  d : (by apply H3)
      ...  <=> e : H4.

import tactic.

infixl 50 => : implies

variables a b c d e : Bool.
axiom H1 : a → b.
axiom H2 : b = c.
axiom H3 : c → d.
axiom H4 : d = e.

theorem T : a → e
:= calc a  =>  b : H1
      ...  =   c : H2
      ...  =>  d : H3
      ...  = e   : H4.

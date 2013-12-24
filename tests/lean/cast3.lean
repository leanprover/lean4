Import "cast.lean"

Variables A A' B B' : Type
Variable x : A
Eval cast (Refl A) x
Eval x = (cast (Refl A) x)
Variable b : B
Definition f (x : A) : B := b
Axiom H : (A -> B) = (A' -> B)
Variable a' : A'
Eval (cast H f) a'
Axiom H2 : (A -> B) = (A' -> B')
Definition g (x : B') : Nat := 0
Eval g ((cast H2 f) a')
Check g ((cast H2 f) a')

Eval (cast H2 f) a'

Variables A1 A2 A3 : Type
Axiom Ha : A1 = A2
Axiom Hb : A2 = A3
Variable a : A1
Eval (cast Hb (cast Ha a))
Check (cast Hb (cast Ha a))

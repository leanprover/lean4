import cast

variables A A' B B' : Type
variable x : A
eval cast (Refl A) x
eval x = (cast (Refl A) x)
variable b : B
definition f (x : A) : B := b
axiom H : (A -> B) = (A' -> B)
variable a' : A'
eval (cast H f) a'
axiom H2 : (A -> B) = (A' -> B')
definition g (x : B') : Nat := 0
eval g ((cast H2 f) a')
check g ((cast H2 f) a')

eval (cast H2 f) a'

variables A1 A2 A3 : Type
axiom Ha : A1 = A2
axiom Hb : A2 = A3
variable a : A1
eval (cast Hb (cast Ha a))
check (cast Hb (cast Ha a))

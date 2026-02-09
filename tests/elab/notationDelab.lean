notation "unitTest " x => Prod.mk x ()

#check unitTest 42

notation "parenthesisTest " x => Nat.sub (x)
#check parenthesisTest 12

def Set (α : Type u) := α → Prop
def setOf {α : Type} (p : α → Prop) : Set α := p
notation "{ " x " | " p " }" => setOf (fun x => p)

#check { (x : Nat) | x ≤ 1 }

notation "cdotTest " "(" x ", " y ")" => Prod.map (· + 1) (1 + ·) (x, y)

#check cdotTest (13, 12)

notation "tupleFunctionTest " "(" x ", " y ")"=> Prod.map (Nat.add 1) (Nat.add 2) (x, y)

#check tupleFunctionTest (15, 12)

notation "doubleRhsTest " x => Prod.mk x x

#check doubleRhsTest 12

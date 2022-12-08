import Lean

def f (x y : Nat) := x * y + 1

infixl:65 " *' " => f

#check 2 *' 3

notation "unitTest " x => Prod.mk x ()

#check unitTest 42

notation "parenthesisTest " x => Nat.sub (x)
#check parenthesisTest 12

def Set (α : Type u) := α → Prop
def setOf {α : Type} (p : α → Prop) : Set α := p
notation "{ " x " | " p " }" => setOf (fun x => p)

#check { x | x ≤ 1 }

notation "cdotTest " "(" x ", " y ")" => Prod.map (· + 1) (1 + ·) (x, y)

#check cdotTest (13, 12)

notation "tupleFunctionTest " "(" x ", " y ")"=> Prod.map (Nat.add 1) (Nat.add 2) (x, y)

#check tupleFunctionTest (15, 12)

notation "diag " x => Prod.mk x x

#check diag 12

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.Prod.mk] def delabDoubleRhsTest : Delab := do
   let e ← getExpr
   let #[_, _, x, y] := e.getAppArgs | failure
   guard (← isDefEq x y) 
   let stx ← withAppArg delab
   `(diag $stx)     

#check diag 3
#check (3, 3)
#check (3, 4)
#check (2+1, 3)
#check (true, true)




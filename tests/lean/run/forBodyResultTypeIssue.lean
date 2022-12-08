abbrev M := ExceptT String <| StateT Nat Id

def f (xs : List Nat) : M Unit := do
for x in xs do
  if x == 0 then
    throw "contains zero"

#eval f [1, 2, 3] |>.run' 0
#eval f [1, 0, 3] |>.run' 0

theorem ex1 : (f [1, 2, 3] |>.run' 0) = Except.ok () :=
rfl

theorem ex2 : (f [1, 0, 3] |>.run' 0) = Except.error "contains zero" :=
rfl

universe u

abbrev N := ExceptT (ULift.{u} String) Id

def idM {α : Type u} (a : α) : N α :=
pure a

def checkEq {α : Type u} [BEq α] [ToString α] (a b : α) : N PUnit := do
unless a == b do
  throw (ULift.up s!"{a} is not equal to {b}")

def g {α : Type u} [BEq α] [ToString α] (xs : List α) (a : α) : N PUnit := do
for x in xs do
  let a ← idM a
  checkEq x a

#eval g [1, (2:Nat), 3] 1 |>.run

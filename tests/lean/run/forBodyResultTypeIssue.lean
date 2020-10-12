new_frontend

abbrev M := ExceptT String $ StateT Nat Id

def f (xs : List Nat) : M Unit := do
for x in xs do
  if x == 0 then
    throw "contains zero"

#eval f [1, 2, 3] $.run' 0
#eval f [1, 0, 3] $.run' 0

theorem ex1 : f [1, 2, 3] $.run' 0 = Except.ok () :=
rfl

theorem ex2 : f [1, 0, 3] $.run' 0 = Except.error "contains zero" :=
rfl



class Inc (α : Type) :=
(inc : α → α)

export Inc (inc)

instance {α} [Inc α] : Inc (List α) :=
{ inc := (·.map inc) }

instance : Inc Nat :=
{ inc := Nat.succ }

#eval inc 10
#eval inc [1, 2, 3]

theorem ex1 : [(1, "hello"), (2, "world")].map (·.1) = [1, 2] :=
rfl

theorem ex2 : [(1, "hello"), (2, "world")].map (·.snd) = ["hello", "world"] :=
rfl

def sum (xs : List Nat) : Nat :=
(·.2) $ Id.run $ StateT.run (s:=0) do
  xs.forM fun x => modify (· + x)

#eval sum [1, 2, 3, 4]

theorem ex3 : sum [1, 2, 3] = 6 :=
rfl

theorem ex4 : sum [1, 2, 3, 4] = 10 :=
rfl

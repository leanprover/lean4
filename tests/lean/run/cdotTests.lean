

class Inc (α : Type) :=
(inc : α → α)

export Inc (inc)

instance {α} [Inc α] : Inc (List α) :=
{ inc := (·.map inc) }

instance : Inc Nat :=
{ inc := Nat.succ }

#guard inc 10 == 11
#guard inc [1, 2, 3] == [2, 3, 4]

theorem ex1 : [(1, "hello"), (2, "world")].map (·.1) = [1, 2] :=
rfl

theorem ex2 : [(1, "hello"), (2, "world")].map (·.snd) = ["hello", "world"] :=
rfl

def sum (xs : List Nat) : Nat :=
(·.2) $ Id.run $ StateT.run (s:=0) do
  xs.forM fun x => modify (· + x)

#guard sum [1, 2, 3, 4] == 10

theorem ex3 : sum [1, 2, 3] = 6 :=
rfl

theorem ex4 : sum [1, 2, 3, 4] = 10 :=
rfl

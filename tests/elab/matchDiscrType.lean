def g (x : Nat) : List (Nat × List Nat) :=
[(x, [x, x]), (x, [])]

def h (x : Nat) : List Nat :=
let xs := g x |>.filter (fun ⟨_, xs⟩ => xs.isEmpty)
xs.map (·.1)

theorem ex1 : g 10 = [(10, [10, 10]), (10, [])] :=
rfl

theorem ex2 : h 10 = [10] :=
rfl

def f1 (n : Nat) := n + 1
def g1 : Bool :=
  let N := fun t => f1 2 + if t % f1 2 = 0 then 1 else 0
  ¬N 0 = f1 2 + if 0 % f1 2 = 0 then 1 else 0

def f2 (n : Nat) := (n + 0) + 1
def g2 : Bool :=
  ¬ (fun _ => f2 2 + if 0 % f2 2 = 0 then 1 else 0) 0 = f2 2 + if 0 % f2 2 = 0 then 1 else 0

/--
info: false
-/
#guard_msgs in
#reduce g2

/--
info: false
-/
#guard_msgs in
#eval g2

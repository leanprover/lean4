def g (f : Nat → Nat) (n : Nat) : Nat :=
  inner n
where
  @[specialize] inner (n : Nat) : Nat :=
    if n = 0 then 0 else g f (n - 1)

def x := g (fun _ => 0) 0


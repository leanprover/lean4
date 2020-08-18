def f (v : Nat) : StateRefT Nat IO Nat := do
IO.println "hello";
modify fun s => s - v;
get

def g : IO Nat :=
(f 5).run' 20

#eval (f 5).run' 20

#eval (do set 100; f 5).run' 0

def f2 : ReaderT Nat (StateRefT Nat IO) Nat := do
v ← read;
IO.println $ "context " ++ toString v;
modify fun s => s + v;
get

#eval (f2.run 10).run' 20

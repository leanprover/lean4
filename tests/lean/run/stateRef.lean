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

def f3 : StateT String (StateRefT Nat IO) Nat := do
s ← get;
n ← getThe Nat;
set (s ++ ", " ++ toString n);
s ← get;
IO.println s;
set (n+1);
getThe Nat

#eval (f3.run' "test").run' 10

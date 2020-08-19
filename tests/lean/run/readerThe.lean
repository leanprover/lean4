abbrev M := ReaderT String $ StateT Nat $ ReaderT Bool $ IO


def f : M Nat := do
s ← read;
IO.println s;
b ← readThe Bool;
IO.println b;
s ← get;
pure s

#eval (f "hello").run' 10 true

def g : M Nat :=
let a : M Nat := adaptTheReader Bool not f;
adaptReader (fun s => s ++ " world") a

#eval (g "hello").run' 10 true

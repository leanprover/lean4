

abbrev M := ReaderT String $ StateT Nat $ ReaderT Bool $ IO


def f : M Nat := do
let s ← read
IO.println s
let b ← readThe Bool
IO.println b
let s ← get
pure s

/--
info: hello
true
---
info: 10
-/
#guard_msgs in
#eval (f "hello").run' 10 true

def g : M Nat :=
let a : M Nat := withTheReader Bool not f
withReader (fun s => s ++ " world") a

/--
info: hello world
false
---
info: 10
-/
#guard_msgs in
#eval (g "hello").run' 10 true

def f (v : Nat) : StateRefT Nat IO Nat := do
IO.println "hello"
modify fun s => s - v
get

def g : IO Nat :=
f 5 |>.run' 20

/--
info: hello
---
info: 15
-/
#guard_msgs in
#eval (f 5).run' 20

/--
info: hello
---
info: 95
-/
#guard_msgs in
#eval (do set 100; f 5 : StateRefT Nat IO Nat).run' 0
def f2 : ReaderT Nat (StateRefT Nat IO) Nat := do
let v ← read
IO.println $ "context " ++ toString v
modify fun s => s + v
get

/--
info: context 10
---
info: 30
-/
#guard_msgs in
#eval (f2.run 10).run' 20

def f3 : StateT String (StateRefT Nat IO) Nat := do
let s ← get
let n ← getThe Nat
set $ s ++ ", " ++ toString n
let s ← get
IO.println s
set (n+1)
getThe Nat

/--
info: test, 10
---
info: 11
-/
#guard_msgs in
#eval (f3.run' "test").run' 10

structure Label {β : Type} (v : β) (α : Type) :=
(val : α)

class HasGetAt {β : Type} (v : β) (α : outParam Type) (m : Type → Type) :=
(getAt : m α)

instance monadState.hasGetAt (β : Type) (v : β) (α : Type) (m : Type → Type) [Monad m] [MonadStateOf (Label v α) m] : HasGetAt v α m :=
{ getAt := do let a ← getThe (Label v α); pure a.val }

export HasGetAt (getAt)

abbrev M := StateRefT (Label 0 Nat) $ StateRefT (Label 1 Nat) $ StateRefT (Label 2 Nat) IO

def f4 : M Nat := do
let a0 : Nat ← getAt 0
let a1 ← getAt 1
let a2 ← getAt 2
IO.println $ "state0 " ++ toString a0
IO.println $ "state1 " ++ toString a1
IO.println $ "state1 " ++ toString a2
pure (a0 + a1 + a2)

/--
info: state0 10
state1 20
state1 30
---
info: 60
-/
#guard_msgs in
#eval f4.run' ⟨10⟩ |>.run' ⟨20⟩ |>.run' ⟨30⟩

abbrev S (ω : Type) := StateRefT Nat $ StateRefT String $ ST ω

def f5 {ω} : S ω Unit := do
let s ← getThe String
modify fun n => n + s.length
pure ()

def f5Pure (n : Nat) (s : String) :=
runST fun _ => f5.run n |>.run s

/-- info: (((), 21), "hello world") -/
#guard_msgs in
#eval f5Pure 10 "hello world"

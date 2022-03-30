namespace Tutorial

/- This file contains the code examples that are used in the
monad control docstring in "How `MonadControl` works" in src/Init/Control/Basic.lean -/

def σ := Nat
@[reducible]
def β := String

constant foo : ∀ {α}, IO α → IO α
constant bar : StateT σ IO β

def mapped_foo : StateT σ IO β := do
  let s ← get
  let (b, s') ← liftM <| foo <| StateT.run bar s
  set s'
  return b

def stM (α : Type) := α × σ

def restoreM (x : IO (stM α)) : StateT σ IO α := do
  let (a,s) ← liftM x
  set s
  return a

def mapped_foo' : StateT σ IO β := do
  let s ← get
  let mapInBase := fun z => StateT.run z s
  restoreM <| foo <| mapInBase bar

def control {α : Type}
  (f : ({β : Type} → StateT σ IO β → IO (stM β)) → IO (stM α))
  : StateT σ IO α := do
  let s ← get
  let mapInBase := fun {β} (z : StateT σ IO β) => StateT.run z s
  let r : IO (stM α) := f mapInBase
  restoreM r

def mapped_foo'' : StateT σ IO β :=
  control (fun mapInBase => foo (mapInBase bar))

end Tutorial

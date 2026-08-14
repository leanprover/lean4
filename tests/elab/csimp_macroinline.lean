module

/-! Tests that `@[csimp]` replacements are applied before `@[macro_inline]` expansion. -/

@[expose] public section

noncomputable def myAnd (a b : Bool) : Bool :=
  Bool.rec false b a

@[macro_inline]
def myAndImpl (a b : Bool) : Bool :=
  match a with
  | false => false
  | true => b

@[csimp]
theorem myAnd_eq_myAndImpl : myAnd = myAndImpl := by
  funext x <;> cases x <;> rfl

def a : Bool :=
  dbg_trace "a"
  false
def b : Bool :=
  dbg_trace "b"
  true

def c : Bool :=
  myAnd a b

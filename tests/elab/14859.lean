module

@[expose] public section

/-! Regression test for issue 14859 on mutual recursion of macro_inline and csimp -/

def specOr (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

@[macro_inline] def implOr (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

@[csimp] theorem specOr_eq_implOr : specOr = implOr := by
  funext x y; cases x <;> rfl

/-- Macro-inlining this introduces `specOr` after `toDecl` has already run `csimp`. -/
@[macro_inline] def wrapper (x y : Bool) : Bool :=
  specOr x y

def useWrapper (x y : Bool) : Bool :=
  wrapper x y

/-- info: false -/
#guard_msgs in
#eval useWrapper false false

/-- info: true -/
#guard_msgs in
#eval useWrapper true false

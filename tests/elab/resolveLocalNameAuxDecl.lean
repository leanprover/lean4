/-!
Name resolution precedence between ordinary locals, auxiliary declarations (`let rec`, `where` and
recursive references) and global declarations: at each prefix of a dotted name the most recent
local binding wins, an ordinary local at any prefix wins over auxiliary declarations and globals,
and an auxiliary declaration competes with globals by longest prefix, winning ties.
-/

set_option linter.unusedVariables false

/-! `let rec` and `where` shadow earlier locals of the same name. -/

def letRecShadows (f : Nat) : Nat :=
  let rec f : Nat := 3
  f

/-- info: 3 -/
#guard_msgs in #eval letRecShadows 5

def letRecShadowsProj (f : Nat) : Nat :=
  let rec f : Nat := 3
  f.succ

/-- info: 4 -/
#guard_msgs in #eval letRecShadowsProj 5

def whereShadows (g : Nat) : Nat := g
where g : Nat := 3

/-- info: 3 -/
#guard_msgs in #eval whereShadows 5

/-! A global matching a longer prefix wins over a projection through an auxiliary declaration. -/

def longer.succ : Nat := 100

def longerGlobal : Nat :=
  let rec longer : Nat := 3
  longer.succ

/-- info: 100 -/
#guard_msgs in #eval longerGlobal

/-! An ordinary local shadowed by an auxiliary declaration stays shadowed when a longer global wins. -/

def shadowed.succ : Nat := 100

def shadowedLocal : Nat :=
  let shadowed : Nat := 5
  let rec shadowed : Nat := 3
  shadowed.succ

/-- info: 100 -/
#guard_msgs in #eval shadowedLocal

/-! An auxiliary declaration wins over a global of the same name. -/

def same : Nat := 1

def sameLength : Nat :=
  same.succ
where
  same : Nat := 10

/-- info: 11 -/
#guard_msgs in #eval sameLength

/-! An ordinary local wins over a global or auxiliary declaration matching a longer prefix. -/

def outer.g : Nat := 7

/--
error: Invalid field `g`: The environment does not contain `Nat.g`, so it is not possible to project the field `g` from an expression
  outer
of type `Nat`
-/
#guard_msgs in
example : Nat :=
  let outer := 5
  outer.g

/--
error: Invalid field `g`: The environment does not contain `Nat.g`, so it is not possible to project the field `g` from an expression
  inner
of type `Nat`
-/
#guard_msgs in
def inner : Nat :=
  let inner := 5
  inner.g
where g : Nat := 7

structure Point where
  x : Nat
  g : Nat

def area (area : Point) : Nat :=
  area.g
where g : Nat := 100

/-- info: 2 -/
#guard_msgs in #eval area ⟨1, 2⟩

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs true

def some_def := 1
def some_rdef : Nat → Nat
  | 0 => 42
  | n + 1 => some_rdef n

/--
warning: This simp argument is unused:
  id_eq

Hint: Omit it from the simp argument list.
  simp ̵[̵i̵d̵_̵e̵q̵]̵
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example : True := by simp [id_eq]

/--
warning: This simp argument is unused:
  id_eq

Hint: Omit it from the simp argument list.
  simp [i̵d̵_̵e̵q̵,̵ ̵and_self]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example : True ∧ True := by simp [id_eq, and_self]


#guard_msgs in example : id True := by simp [id_eq]

/--
warning: This simp argument is unused:
  some_def

Hint: Omit it from the simp argument list.
  simp ̵[̵s̵o̵m̵e̵_̵d̵e̵f̵]̵
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : True := by simp [some_def]

#guard_msgs in example : 0 < some_def := by simp [some_def]


-- Duplicate are not warned about (yet)
#guard_msgs in example : 0 < some_def := by simp [some_def, some_def]

-- The diffing algorithm can be somewhat confusing if a simp argument is repeated:

/--
warning: This simp argument is unused:
  some_def.eq_def

Hint: Omit it from the simp argument list.
  simp [some_def, some_def.eq_def,̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
---
warning: This simp argument is unused:
  some_def.eq_def

Hint: Omit it from the simp argument list.
  simp [some_def, some_def.eq_def,̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : 0 < some_def := by simp [some_def, some_def.eq_def, some_def.eq_def]

/--
warning: This simp argument is unused:
  (some_def.eq_def)

Hint: Omit it from the simp argument list.
  simp [some_def, (̵some_def.eq_def)̵,̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
---
warning: This simp argument is unused:
  some_def.eq_def

Hint: Omit it from the simp argument list.
  simp [some_def, (some_def.eq_def),̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : 0 < some_def := by simp [some_def, (some_def.eq_def), some_def.eq_def]

#guard_msgs in example : 0 < some_def := by simp [some_def.eq_def]

#guard_msgs in example : 0 < some_rdef 10 := by simp [some_rdef]

/-- error: simp made no progress -/
#guard_msgs in example : 0 < some_def := by simp [some_rdef]

/--
error: unsolved goals
⊢ 0 < some_def
---
warning: This simp argument is unused:
  some_rdef

Hint: Omit it from the simp argument list.
  simp -failIfUnchanged ̵[̵s̵o̵m̵e̵_̵r̵d̵e̵f̵]̵
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : 0 < some_def := by simp -failIfUnchanged [some_rdef]

#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef]

#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef.eq_def]

/--
warning: This simp argument is unused:
  some_rdef.eq_def

Hint: Omit it from the simp argument list.
  simp -failIfUnchanged [some_rdef,̵ ̵s̵o̵m̵e̵_̵r̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef, some_rdef.eq_def]

#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef, some_rdef.eq_1]

#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef.eq_1, some_rdef.eq_2]

-- This could complain about some_rdef.eq_2, but does not yet:

#guard_msgs in example : 0 < some_rdef 0 := by simp -failIfUnchanged [some_rdef.eq_1, some_rdef.eq_2]

/--
error: unsolved goals
⊢ 0 < some_rdef 10
-/
#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged



/--
error: unsolved goals
a : Nat
h : a = 1
⊢ 0 < a
-/
#guard_msgs in example (a : Nat) (h : a = 1) : 0 < a := by simp -failIfUnchanged

#guard_msgs in example (a : Nat) (h : a = 1) : 0 < a := by simp -failIfUnchanged [h]

-- Local hyps

/--
warning: This simp argument is unused:
  _h

Hint: Omit it from the simp argument list.
  simp -failIfUnchanged ̵[̵_̵h̵]̵
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example (a : Nat) (_h : a = 1) : True := by simp -failIfUnchanged [_h]

#guard_msgs in example (a : Nat) (_h : a = 1) : True := by simp -failIfUnchanged [*]


-- Simprocs

#guard_msgs in example : if true then True else False := by simp only [↓reduceIte]

/--
warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [↓reduceI̵t̵e̵,̵ ̵↓̵r̵e̵d̵u̵c̵e̵DIte]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : if _ : true then True else False := by simp only [↓reduceIte, ↓reduceDIte]

-- Lets

/--
error: unsolved goals
x : Nat := 1
⊢ 0 < x
-/
#guard_msgs in example : let x := 1; x > 0 := by intro x; simp

#guard_msgs in example : let x := 1; x > 0 := by intro x; simp [x]

#guard_msgs in example : let x := 1; True ∨ x > 0:= by intro x; simp [x]

/--
warning: This simp argument is unused:
  x

Hint: Omit it from the simp argument list.
  simp ̵[̵x̵]̵
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in example : let x := 1; True ∨ x > 0:= by intro x; left; simp [x]


-- Now the tests for multiple branches

/--
warning: This simp argument is unused:
  h3

Hint: Omit it from the simp argument list.
  simp [h1, h2,̵ ̵h̵3̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example (h1 : P) (h2 : Q) (h3 : R) : P ∧ (Q ∨ R) := by
  constructor <;> ((try left); simp [h1, h2, h3])

/--
warning: This simp argument is unused:
  h2

Hint: Omit it from the simp argument list.
  simp [h1,̵ ̵h̵2̵]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
---
warning: This simp argument is unused:
  h1

Hint: Omit it from the simp argument list.
  simp [h1̵,̵ ̵h̵2]
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example (h1 : P) (h2 : Q) : P ∧ Q := by
  constructor
  · simp [h1, h2]
  · simp [h1, h2]

-- Inside a macro?

macro "mySimp" h:term : tactic => `(tactic| simp [$h:term, id_eq])
macro tk:"mySimp'" h:term : tactic => `(tactic| simp%$tk [$h:term, id_eq])

/--
warning: This simp argument is unused:
  h

Hint: Omit it from the simp argument list.
  simp ̵[̵h̵]̵
note: this linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example {P : Prop} (h : P) : True ∧ True := by constructor <;> simp [h]

example {P : Prop} (h : P) : True ∧ True := by constructor <;> mySimp h

example {P : Prop} (h : P) : True ∧ True := by constructor <;> mySimp' h


-- Check option setting

section
set_option linter.unusedSimpArgs true

#guard_msgs in
set_option linter.unusedSimpArgs false in
example : True := by
  simp [not_false_eq_true]
end

section
set_option linter.unusedSimpArgs true

#guard_msgs in
example : True := by
  set_option linter.unusedSimpArgs false in
  simp [not_false_eq_true]
end

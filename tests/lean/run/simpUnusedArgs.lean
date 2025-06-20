set_option tactic.simp.warnUnused true

def some_def := 1
def some_rdef : Nat → Nat
  | 0 => 42
  | n + 1 => some_rdef n

/--
warning: This simp argument is unused:
  id_eq

Hint: Omit it from the simp argument list.
  simp ̵[̵i̵d̵_̵e̵q̵]̵
-/
#guard_msgs in
example : True := by simp [id_eq]

/--
warning: This simp argument is unused:
  id_eq

Hint: Omit it from the simp argument list.
  simp [i̵d̵_̵e̵q̵,̵ ̵and_self]
-/
#guard_msgs in
example : True ∧ True := by simp [id_eq, and_self]


#guard_msgs in example : id True := by simp [id_eq]

/--
warning: This simp argument is unused:
  some_def

Hint: Omit it from the simp argument list.
  simp ̵[̵s̵o̵m̵e̵_̵d̵e̵f̵]̵
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
---
warning: This simp argument is unused:
  some_def.eq_def

Hint: Omit it from the simp argument list.
  simp [some_def, some_def.eq_def,̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
-/
#guard_msgs in example : 0 < some_def := by simp [some_def, some_def.eq_def, some_def.eq_def]

/--
warning: This simp argument is unused:
  (some_def.eq_def)

Hint: Omit it from the simp argument list.
  simp [some_def, (̵some_def.eq_def)̵,̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
---
warning: This simp argument is unused:
  some_def.eq_def

Hint: Omit it from the simp argument list.
  simp [some_def, (some_def.eq_def),̵ ̵s̵o̵m̵e̵_̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
-/
#guard_msgs in example : 0 < some_def := by simp [some_def, (some_def.eq_def), some_def.eq_def]

#guard_msgs in example : 0 < some_def := by simp [some_def.eq_def]

#guard_msgs in example : 0 < some_rdef 10 := by simp [some_rdef]

/-- error: simp made no progress -/
#guard_msgs in example : 0 < some_def := by simp [some_rdef]

/--
warning: This simp argument is unused:
  some_rdef

Hint: Omit it from the simp argument list.
  simp -failIfUnchanged ̵[̵s̵o̵m̵e̵_̵r̵d̵e̵f̵]̵
---
error: unsolved goals
⊢ 0 < some_def
-/
#guard_msgs in example : 0 < some_def := by simp -failIfUnchanged [some_rdef]

#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef]

#guard_msgs in example : 0 < some_rdef 10 := by simp -failIfUnchanged [some_rdef.eq_def]

/--
warning: This simp argument is unused:
  some_rdef.eq_def

Hint: Omit it from the simp argument list.
  simp -failIfUnchanged [some_rdef,̵ ̵s̵o̵m̵e̵_̵r̵d̵e̵f̵.̵e̵q̵_̵d̵e̵f̵]
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

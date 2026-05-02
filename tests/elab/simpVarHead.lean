section
theorem broken1 (x : Nat) : x = x + 0 := by simp

/--
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
-/
#guard_msgs in
attribute [local simp] broken1
end

section
theorem broken2 (x : Nat) : x + 0 = x := by simp

-- Works in the usual direction
attribute [local simp] broken2

-- Breaks in the other direction
/--
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
-/
#guard_msgs in
attribute [local simp ←] broken2
end

theorem broken3 (x : Nat → Nat) : x 0 = x 0 + 0 := by simp

/--
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
-/
#guard_msgs in
attribute [simp] broken3

theorem broken4 (x : Nat → Nat) : x 0 + 0 = x 0 := by rfl

/--
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
-/
#guard_msgs in
attribute [simp ←] broken4

section
/--
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
-/
#guard_msgs in
@[local simp] theorem broken5 (x : Prop) : x ↔ x ∧ True := by simp
end

theorem broken6 (x : Prop → Prop) : x False ∧ True ↔ x False := by simp

/--
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
-/
#guard_msgs in
attribute [simp ←] broken6

-- Abbrev as head symbol should not trigger the warning (mathlib false positive regression test)
structure Foo where
  val : Nat

abbrev Foo.get (f : Foo) : Nat := f.val

theorem Foo.get_mk (n : Nat) : (Foo.mk n).get = n := rfl

#guard_msgs in
attribute [simp] Foo.get_mk

-- `.other` head key: lambda as LHS head
theorem broken8 : (fun x : Nat => x + 0) = (fun x => x) := by ext; omega

/--
warning: Left-hand side of simp theorem is headed by a `.other` key in the discrimination tree (e.g. because it is a lambda expression). This theorem will be tried against all expressions that also have a `.other` key as head, which can cause slowdowns. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.otherHead false` to disable this warning.
-/
#guard_msgs in
attribute [simp] broken8

-- Option to disable the `.other` head warning
section
#guard_msgs in
set_option warning.simp.otherHead false in
attribute [local simp] broken8
end

-- Option to disable the warning
section
theorem broken7 (x : Nat) : x = x + 0 := by omega

#guard_msgs in
set_option warning.simp.varHead false in
attribute [local simp] broken7
end

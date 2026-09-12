/-!
  # The `linter.blanketSimpArgs` linter

  The left-hand side of `eq_zero` below is the variable `a`, so `simp [eq_zero]` retrieves
  `eq_zero` at every subterm it visits and synthesizes `OfNat` and `Subsingleton` instances at
  each match. Writing `eq_zero (α := α)` or `eq_zero x` synthesizes those instances once instead,
  while elaborating the argument.
-/

-- The test harness runs with `linter.all=false`.
set_option linter.blanketSimpArgs true

theorem eq_zero {α : Type} [OfNat α 0] [Subsingleton α] (a : α) : a = (0 : α) :=
  Subsingleton.elim ..

/--
warning: The left-hand side of this theorem is a variable, so `simp` retrieves the theorem at every visited subterm and synthesizes its instance arguments at each match:
  eq_zero
Fixing the implicit arguments, as in `(α := Nat)`, or applying the theorem to a term synthesizes those instances once instead, while the theorem is elaborated.

Note: This linter can be disabled with `set_option linter.blanketSimpArgs false`
-/
#guard_msgs in
example {α : Type} [OfNat α 0] [Subsingleton α] (x : α) : x = 0 := by
  simp [eq_zero]

-- Fixing the implicit arguments determines the side conditions once, so the argument is
-- confined to that type.
#guard_msgs in
example {α : Type} [OfNat α 0] [Subsingleton α] (x : α) : x = 0 := by
  simp [eq_zero (α := α)]

-- Applying the theorem to a term likewise.
#guard_msgs in
example {α : Type} [OfNat α 0] [Subsingleton α] (x : α) : x = 0 := by
  simp [eq_zero x]

-- A left-hand side of fixed type only matches subterms of that type, so the instance surviving
-- elaboration is synthesized at one type throughout.
class Foo (n : Nat) : Prop where dummy : True
instance : Foo 0 := ⟨trivial⟩

theorem ground_inst [Foo 0] (a : Nat) : a + 0 = a := Nat.add_zero a

#guard_msgs in
example (n : Nat) : n + 0 = n := by
  simp [ground_inst]

-- An ordinary rewrite has a head symbol in its key.
#guard_msgs in
example (n : Nat) : id n = n := by
  simp [id_eq]

-- Definitions passed to `simp` are unfolded rather than used as rewrites, so a result type
-- that is a variable, as in `Or.by_cases`, does not make them blanket rewrites.
def fallback {α : Type} [Inhabited α] (_ : Nat) : α := default

#guard_msgs in
example : fallback (α := Nat) 3 = default := by
  simp [fallback]

-- The linter can be turned off.
set_option linter.blanketSimpArgs false in
#guard_msgs in
example {α : Type} [OfNat α 0] [Subsingleton α] (x : α) : x = 0 := by
  simp [eq_zero]

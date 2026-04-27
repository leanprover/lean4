-- This uses `def` for a Prop — the `defLemma` linter should flag this.
def shouldBeTheorem : 1 = 1 := rfl

-- This is annotated to be skipped by `defLemma` — no import needed.
@[builtin_nolint defLemma]
def skippedViolation : 2 = 2 := rfl

-- A `@[reducible, instance] def` of Prop type is still elaborated as a `def`,
-- so `defLemma` should flag it.
@[reducible, instance]
def reducibleInstShouldBeTheorem : Nonempty Bool := ⟨true⟩

-- A plain `instance` of Prop type is elaborated as a `theorem`, so it should
-- not be flagged.
instance plainInstIsOk : Nonempty String := ⟨""⟩

-- Bad universe levels — the `checkUnivs` linter should flag this.
universe u v in
def badUnivDecl (α : Type (max u v)) : Type (max u v) := α

-- Annotated to be skipped by `checkUnivs`.
universe u v in
@[builtin_nolint checkUnivs]
def badUnivSkipped (α : Type (max u v)) : Type (max u v) := α

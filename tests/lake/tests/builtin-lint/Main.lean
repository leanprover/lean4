import Main.Sub

-- `linter.defProp` and `linter.checkUnivs` are off by default for bootstrapping
-- reasons; enable them here so the test scenarios that exercise default lint
-- mode still trigger them.
set_option linter.defProp true
set_option linter.checkUnivs true

-- This uses `def` for a Prop — the `defProp` linter should flag this.
def shouldBeTheorem : 1 = 1 := rfl

-- `set_option` disables `defProp` locally so this violation is not flagged.
set_option linter.defProp false in
def skippedViolation : 2 = 2 := rfl

-- A `@[reducible, instance] def` of Prop type is still elaborated as a `def`,
-- so `defProp` should flag it.
@[reducible, instance]
def reducibleInstShouldBeTheorem : Nonempty Bool := ⟨true⟩

-- A plain `instance` of Prop type is elaborated as a `theorem`, so it should
-- not be flagged.
instance plainInstIsOk : Nonempty String := ⟨""⟩

-- Bad universe levels — the `checkUnivs` linter should flag this.
universe u v in
def badUnivDecl (α : Type (max u v)) : Type (max u v) := α

-- `set_option` disables `checkUnivs` locally so this violation is not flagged.
set_option linter.checkUnivs false in
universe u v in
def badUnivSkipped (α : Type (max u v)) : Type (max u v) := α

import Linters

-- `linter.defProp` is off by default for bootstrapping reasons; enable it
-- here so `shouldBeTheoremUnderExtra` still fires when default linters run.
set_option linter.defProp true

-- This name ends with 'Extra' — the `dummyExtra` env linter should flag it
-- whenever `linter.dummyExtra` is enabled for this build.
def badNameExtra : Nat := 1

-- This name also ends with 'Extra', but the linter is disabled for this
-- declaration via `set_option ... false in`, recording `false` in its
-- snapshot. This is the replacement for the old `builtin_nolint` attribute.
set_option linter.dummyExtra false in
def skippedNameExtra : Nat := 1

-- The `<;>` here is unnecessary because `skip` produces only one subgoal —
-- `skip; skip` would do the same thing. The builtin extra
-- `unnecessarySeqFocus` text linter should flag it.
example : True := by
  skip <;> skip
  trivial
-- The component `Dup` appears consecutively in this declaration's name —
-- the builtin extra `dupNamespace` text linter should flag it.
def Dup.Dup.violation : Nat := 2

-- This uses `def` for a Prop — the default `defProp` linter should flag this
-- whenever default linters run.
def shouldBeTheoremUnderExtra : 1 = 1 := rfl

-- The `done` here is unreachable because `trivial` produces no subgoals.
-- The builtin extra `unreachableTactic` text linter should flag it.
def unreachableTacticViolation : True := by trivial <;> done

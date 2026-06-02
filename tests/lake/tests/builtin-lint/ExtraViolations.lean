import Linters

-- `linter.defProp` is off by default for bootstrapping reasons; enable it
-- here so `shouldBeTheoremUnderExtra` still fires when default linters run.
set_option linter.defProp true

-- This name ends with 'Extra' — the dummyExtra linter should flag it.
def badNameExtra : Nat := 1

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
-- whenever default linters run, including under `--extra`.
def shouldBeTheoremUnderExtra : 1 = 1 := rfl

-- The `done` here is unreachable because `trivial` produces no subgoals.
-- The builtin extra `unreachableTactic` text linter should flag it.
def unreachableTacticViolation : True := by trivial <;> done

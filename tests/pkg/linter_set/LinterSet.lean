import LinterSet.Def

open Lean Linter

def fooInitially : MetaM Unit := do
  -- linter.foo1 and linter.foo2 are declared to be false by default
  assert! !(getLinterValue linter.foo1 (← getLinterOptions))
  assert! !(getLinterValue linter.foo2 (← getLinterOptions))
  -- linter.foo_true is declared to be true by default
  assert! (getLinterValue linter.foo_true (← getLinterOptions))
  pure ()

#eval fooInitially

set_option linter.set.foo true

def fooSetTrue : MetaM Unit := do
  -- All linters in the `foo` set should now be true
  assert! (getLinterValue linter.foo1 (← getLinterOptions))
  assert! (getLinterValue linter.foo2 (← getLinterOptions))
  assert! (getLinterValue linter.foo_true (← getLinterOptions))
  pure ()

#eval fooSetTrue

section OverrideFalse

set_option linter.foo2 false

def overrideFalse : MetaM Unit := do
  -- The overridden linter should now be false.
  assert! (getLinterValue linter.foo1 (← getLinterOptions))
  assert! !(getLinterValue linter.foo2 (← getLinterOptions))
  assert! (getLinterValue linter.foo_true (← getLinterOptions))
  pure ()

#eval overrideFalse

end OverrideFalse

section AllFalse

set_option linter.all false

def allSetFalse : MetaM Unit := do
  -- All linters, including those in the `foo` set, should now be false
  assert! !(getLinterValue linter.foo1 (← getLinterOptions))
  assert! !(getLinterValue linter.foo2 (← getLinterOptions))
  assert! !(getLinterValue linter.foo_true (← getLinterOptions))
  pure ()

#eval allSetFalse

end AllFalse

set_option linter.set.foo false

def fooSetFalse : MetaM Unit := do
 -- All linters in the `foo` set should now be back to default.
  assert! !(getLinterValue linter.foo1 (← getLinterOptions))
  assert! !(getLinterValue linter.foo2 (← getLinterOptions))
  assert! (getLinterValue linter.foo_true (← getLinterOptions))
  pure ()

#eval fooSetFalse

section AllTrue

set_option linter.all true

/-- Running this code will check that all linters in the `foo` set are true.

This docstring is required due to `linter.all` being true(!). -/
def allSetTrue : MetaM Unit := do
  -- All linters, including those in the `foo` set, should now be true
  assert! (getLinterValue linter.foo1 (← getLinterOptions))
  assert! (getLinterValue linter.foo2 (← getLinterOptions))
  assert! (getLinterValue linter.foo_true (← getLinterOptions))
  pure ()

#eval allSetTrue

end AllTrue

/-! Test setting user options from lakefile. -/

open Lean

def barFromLakefile : MetaM Unit := do
  assert! (getLinterValue linter.bar (← getLinterOptions))

#eval barFromLakefile


import Linters

-- This name ends with 'Clippy' — the dummyClippy linter should flag it.
def badNameClippy : Nat := 1

-- The component `Dup` appears consecutively in this declaration's name —
-- the builtin clippy `dupNamespace` env linter should flag it.
def Dup.Dup.violation : Nat := 2

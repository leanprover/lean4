module

-- Deliberately does NOT import `Linters` or `Main.Rules`; those are supplied
-- to the lint run via `--checks` / `lintChecks` instead.

public def shouldBeFlaggedDummyMarker : Nat := 1

public def mainViolationRulesMarker : Nat := 2

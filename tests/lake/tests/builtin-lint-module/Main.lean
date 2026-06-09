module

public import Linters

-- Public def whose name ends with the dummy linter's marker suffix. The
-- dummy env linter (registered in `Linters.lean`, default-on) reads only
-- the declaration name, so it does not depend on bodies being exposed at
-- the `.exported` import level. This proves env linters still see imported
-- public decls after the level switch.
public def shouldBeFlaggedDummyMarker : Nat := 1

-- Public def with an unused let. `linter.unusedVariables` (default-on)
-- fires during the build, the warning is captured in `lintLogExt`, and
-- `lake lint` re-emits it. `lintLogExt` writes uniform OLean entries, so
-- this must survive loading at `.exported`.
public def publicUnusedVarFixture : Nat :=
  let publicUnusedLet := 5
  3

-- Private def with an unused let. Private declarations are elided from
-- `env.constants` at the `.exported` import level, so env linters cannot
-- see them. The text-linter warning is fundamentally different: it fires
-- at elaboration time and is stored in `lintLogExt` keyed by module
-- index, not by declaration. The entry therefore survives the level
-- change and must still be replayed by `lake lint`.
private def privateUnusedVarFixture : Nat :=
  let privateUnusedLet := 7
  3

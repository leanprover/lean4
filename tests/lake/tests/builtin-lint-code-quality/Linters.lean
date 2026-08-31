import Lean.Linter.EnvLinter

open Lean Meta Lean.Linter Lean.Elab.Command

/-- Option gating the dummy env linter; on by default so it fires during the
build without needing `--linters`. -/
register_option linter.dummyMarker : Bool := {
  defValue := true
  descr := "(test) flag declarations whose name ends with 'DummyMarker'"
}

initialize addEnvLinterOption linter.dummyMarker

-- A dummy env linter flagging any declaration whose name ends with "DummyMarker".
-- Exercises the env-linter side of the code quality output independently of any
-- production env linter.
@[builtin_env_linter linter.dummyMarker]
public meta def dummyMarker : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'DummyMarker' found."
  errorsFound := "DUMMY MARKER VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "DummyMarker" then
      return some "declaration name ends with 'DummyMarker'"
    return none

/-- Option gating the metric-recording text linter; on by default so entries are recorded
during the build without needing `--linters`. -/
register_option linter.declMetric : Bool := {
  defValue := true
  descr := "(test) record a code quality entry for every declaration command"
}

-- A text linter recording code quality entries for every `declaration` command, attributed to
-- the elaborating module. Exercises the recorded-metrics side of the code quality output: the
-- entries are persisted into the `.olean` during the build and recovered by
-- `lake lint --code-quality` without re-elaboration. `declCommands` is gated by (and attributed
-- to) `linter.declMetric`, so linter selection flags apply to it; `declCommandsRaw` is logged
-- unconditionally without attribution, so no linter selection flag can suppress it.
def declMetricLinter : Linter where
  run cmdStx := do
    unless cmdStx.getKind == ``Lean.Parser.Command.declaration do return
    logCodeQualityEntryIf linter.declMetric
      { name := "declCommands", source := .module (← getMainModule), value := .scalar 1.0 }
    logCodeQualityEntry
      { name := "declCommandsRaw", source := .module (← getMainModule), value := .scalar 1.0 }

initialize addLinter declMetricLinter

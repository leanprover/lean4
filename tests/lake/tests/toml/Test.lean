/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml
import Lake.Util.Message
import Lake.Toml.Data.Value

/-!
## TOML Test Runner

Tests Lake's TOML implementation against the version of the [toml-test][1]
compliance suite stored in `tests` (currently, suite v1.4.0 for TOML v1.0.0).

[1]: https://github.com/toml-lang/toml-test
-/

open Lake Toml
open Lean Parser System

inductive TomlOutcome where
| pass (t : Table)
| fail (log : MessageLog)
| error (e : IO.Error)

nonrec def loadToml (tomlFile : FilePath) : BaseIO TomlOutcome := do
  let fileName := tomlFile.fileName.getD tomlFile.toString
  let input ←
    match (← IO.FS.readBinFile tomlFile |>.toBaseIO) with
    | .ok bytes =>
      if let some input := String.fromUTF8? bytes then
        pure input.crlfToLf
      else
        return .fail <| MessageLog.empty.add
          {fileName, pos := ⟨1,0⟩, data := m!"file contains invalid characters"}
    | .error e => return .error e
  let ictx := mkInputContext input fileName
  match (← loadToml ictx |>.toBaseIO) with
  | .ok table => return .pass table
  | .error log => return .fail log

inductive TestOutcome
| skip
| pass (s : String)
| fail (s : String)
| error (e : String)

def testInvalid (tomlFile : FilePath) : BaseIO TestOutcome := do
  match (← loadToml tomlFile) with
  | .pass t => return .fail (ppTable t)
  | .fail l => return .pass (← mkMessageLogString l)
  | .error e => return .error (toString e)

/-- Given `actual`, verify that it is equal to `expected` via `BEq`. -/
@[inline] def checkBEq [BEq α] [ToString α] (actual expected : α) : Except String Unit := do
  unless actual == expected do
    throw s!"expected '{expected}', got '{actual}'"

/--
Given a primitive TOML value of type `actualTy`,
verify that it was expected and return the expected value (as a `String`).
-/
def checkPrimitive (actualTy : String) (expected : Json) : Except String String := do
  let .ok expected := expected.getObj?
    | throw s!"expected non-primitive, got '{actualTy}'"
  let some ty := expected.get?  "type"
    | throw s!"expected non-primitive, got '{actualTy}'"
  let some val := expected.get? "value"
    | throw s!"expected non-primitive, got '{actualTy}'"
  let .ok val := val.getStr?
    | throw s!"expected non-primitive, got '{actualTy}'"
  unless actualTy == ty do
    throw s!"expected value of type '{ty}', got '{actualTy}'"
  return val

def decodeSign (s : String) : Bool × String.Slice :=
  if s.front == '-' then
    (true, s.drop 1)
  else if s.front == '+' then
    (false, s.drop 1)
  else
    (false, s.toSlice)

mutual

/-- Given a TOML value `actual`, verify that it was expected. -/
partial def checkValue (actual : Value) (expected : Json) : Except String Unit := do
  match actual with
  | .boolean _ b => checkBEq (toString b) (← checkPrimitive "bool" expected)
  | .string _ s => checkBEq s (← checkPrimitive "string" expected)
  | .integer _ n => checkBEq (toString n) (← checkPrimitive "integer" expected)
  | .float _ actN =>
    let expected ← checkPrimitive "float" expected
    if expected.toSlice.eqIgnoreAsciiCase "nan".toSlice then
      unless actN.isNaN do
        throw s!"expected '{expected}', got '{actN}'"
    else
      let (neg, e) := decodeSign expected
      if e.eqIgnoreAsciiCase "inf".toSlice then
        unless actN.isInf && neg == (actN < 0) do
          throw s!"expected '{e}', got '{actN}'"
      else
          let some flt :=
            (Nat.toFloat <$> e.toNat?) <|>
            (Syntax.decodeScientificLitVal? e.copy |>.map fun (m,s,e) => Float.ofScientific m s e)
            | throw s!"failed to parse expected float value: {e}"
          checkBEq actN <| if neg then -flt else flt
  | .dateTime _ dt =>
    match dt with
    | .offsetDateTime _ _ _ => checkBEq (toString dt) (← checkPrimitive "datetime" expected)
    | .localDateTime .. =>  checkBEq (toString dt) (← checkPrimitive "datetime-local" expected)
    | .localDate d => checkBEq (toString d) (← checkPrimitive "date-local" expected)
    | .localTime t => checkBEq (toString t) (← checkPrimitive "time-local" expected)
  | .array _ actVs =>
    let .ok expVs := expected.getArr?
      | throw "expected non-array, got array"
    if h_size : actVs.size = expVs.size then
      actVs.size.forM fun i _ => checkValue actVs[i] expVs[i]
    else
      throw s!"expected array of size {expVs.size}, got {actVs.size}:\n{actual}"
  | .table _ t => checkTable t expected

/-- Given a TOML table `actual`, verify that it was expected. -/
partial def checkTable (actual : Table) (expected : Json) : Except String Unit := do
  let .ok expected := expected.getObj?
    | throw "expected non-table, got table"
  if actual.size != expected.size then
    throw s!"expected table of size {expected.size}, got {actual.size}:\n{ppTable actual}"
  for ⟨k,expV⟩ in expected do
    let some actV := actual.find? (Name.mkSimple k)
      | throw s!"expected key '{k}'"
    try checkValue actV expV catch e => throw s!"{k}: {e}"

end

def testValid (tomlFile : FilePath) : BaseIO TestOutcome := do
  match (← loadToml tomlFile) with
  | .pass actualTable =>
    match (← IO.FS.readFile (tomlFile.withExtension "json") |>.toBaseIO) with
    | .ok contents =>
      match Json.parse contents with
      | .ok expected =>
        match checkTable actualTable expected with
        | .ok _ => return .pass <| ppTable actualTable
        | .error e => return .fail <| e.trimAsciiEnd.copy.push '\n'
      | .error e => return .error s!"invalid JSON: {e}"
    | .error e => return .error (toString e)
  | .fail log => return .fail (← mkMessageLogString log)
  | .error e => return .error (toString e)

def walkDir (root : FilePath) (ext : String := "toml") : IO (Array FilePath) := do
  (← root.walkDir).filterM fun path => do
    return path.extension == some ext && !(← path.isDir)

def main : IO UInt32 := do
  -- Detect Tests
  let validTestFiles ← walkDir <| "tests" / "valid"
  let invalidTestFiles ← walkDir <| "tests" / "invalid"
  let numTests := validTestFiles.size + invalidTestFiles.size
  -- Run Tests
  let outcomes := Array.mkEmpty numTests
  let outcomes ← invalidTestFiles.foldlM (init := outcomes) fun outcomes path => do
    return outcomes.push (← IO.FS.realPath path, ← testInvalid path)
  let outcomes ← validTestFiles.foldlM (init := outcomes) fun outcomes path => do
    return outcomes.push (← IO.FS.realPath path, ← testValid path)
  -- Print Results
  let showPassedTests := false
  let showOutputOnFail := true
  let mut skipped := 0; let mut failed := 0; let mut errored := 0
  for (testName, outcome) in outcomes do
    match outcome with
    | .skip =>
      skipped := skipped + 1
    | .pass s =>
      if showPassedTests then
        IO.print s!"{testName} passed:\n{s}"
    | .fail s =>
      failed := failed + 1
      if showOutputOnFail && !s.isEmpty then
        IO.print s!"{testName} failed:\n{s}"
      else
        IO.print s!"{testName} failed\n"
    | .error s =>
      errored := errored + 1
      IO.print s!"{testName} errored:\n{s}\n"
  let percent := (numTests - skipped - failed - errored) * 100 / numTests
  IO.println s!"{percent}% of tests passed, \
    {failed} failed, {errored} errored, {skipped} skipped out of {numTests}"
  return if failed > 0 || errored > 0 then 1 else 0

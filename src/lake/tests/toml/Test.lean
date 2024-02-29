/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml

/-!
## TOML Test Runner

Tests Lake's TOML implementation against the version of the [toml-test][1]
compliance suite stored in `tests` (currently, suite v1.4.0 for TOML v1.0.0).

[1]: https://github.com/toml-lang/toml-test
-/

open Lake.Toml
open Lean Parser System

inductive TomlOutcome where
| pass (t : Table)
| fail (log : MessageLog)
| error (e : IO.Error)

def mkParserErrorMessage (ictx : InputContext) (s : ParserState) (e : Parser.Error) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition s.pos
  endPos := none
  keepFullRange := true
  data := toString e

def mkErrorMessage (ictx : InputContext) (e : Exception) : Message where
  fileName := ictx.fileName
  pos := ictx.fileMap.toPosition <| e.getRef.getPos?.getD 0
  endPos := ictx.fileMap.toPosition <$> e.getRef.getTailPos?
  keepFullRange := true
  data := e.toMessageData

@[inline] def Fin.allM [Monad m] (n) (f : Fin n → m Bool) : m Bool :=
  loop 0
where
  loop (i : Nat) : m Bool := do
    if h : i < n then
      if (← f ⟨i, h⟩) then loop (i+1) else pure false
    else
      pure true
  termination_by n - i

@[inline] def Fin.all (n) (f : Fin n → Bool) : Bool :=
  Id.run <| allM n f

@[inline] def Fin.forM [Monad m] (n) (f : Fin n → m Unit) : m Unit :=
  loop 0
where
  loop (i : Nat) : m Unit := do
    if h : i < n then let a ← f ⟨i, h⟩; loop (i+1) else pure ()
  termination_by n - i

def bytesBEq (a b : ByteArray) : Bool :=
  if h_size : a.size = b.size then
    Fin.all a.size fun i => a[i] = b[i]'(h_size ▸ i.isLt)
  else
    false

def mkValidString (s : String) : String :=
  s.foldl (init := "") fun s c => s.push c

def parseToml (tomlFile : FilePath) : BaseIO TomlOutcome := do
  let fileName := tomlFile.fileName.getD tomlFile.toString
  let input ←
    match (← IO.FS.readBinFile tomlFile |>.toBaseIO) with
    | .ok bytes =>
      let input := String.fromUTF8Unchecked bytes
      if bytesBEq (mkValidString input).toUTF8 bytes then
        pure input
      else
        return .fail <| MessageLog.empty.add
          {fileName, pos := ⟨1,0⟩, data := m!"file contains invalid characters"}
    | .error e => return .error e
  let ictx := mkInputContext input fileName
  let env ←
    match (← mkEmptyEnvironment.toBaseIO) with
    | .ok env => pure env
    | .error e => return .error e
  let s := toml.fn.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if let some errorMsg := s.errorMsg then
    return .fail <| MessageLog.empty.add <| mkParserErrorMessage ictx s errorMsg
  else if input.atEnd s.pos then
    let act := elabToml ⟨s.stxStack.back⟩
    match (← act.run {fileName, fileMap := ictx.fileMap} {env} |>.toBaseIO) with
    | .ok (t, s) =>
      if s.messages.hasErrors then
        return .fail s.messages
      else
        return .pass t
    | .error e =>
      return .fail <| MessageLog.empty.add <| mkErrorMessage ictx e
  else
    return .fail <| MessageLog.empty.add <| mkParserErrorMessage ictx s {expected := ["end of input"]}

inductive TestOutcome
| skip
| pass (s : String)
| fail (s : String)
| error (e : String)

def mkMessageStringCore
  (severity : MessageSeverity)
  (fileName caption body : String)
  (pos : Position) (endPos? : Option Position := none)
  (infoWithPos := false)
: String := Id.run do
  let mut str := body
  unless caption == "" do
    str := caption ++ ":\n" ++ str
  match severity with
  | .information =>
    if infoWithPos then
      str := mkErrorStringWithPos fileName pos (endPos := endPos?) "info: " ++ str
  | .warning =>
    str := mkErrorStringWithPos fileName pos (endPos := endPos?) "warning: " ++ str
  | .error =>
    str := mkErrorStringWithPos fileName pos (endPos := endPos?) "error: " ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str

def mkMessageString (msg : Message) (includeEndPos := false) (infoWithPos := false) : BaseIO String := do
  let endPos? := if includeEndPos then msg.endPos else none
  match (← msg.data.toString.toBaseIO) with
  | .ok s =>
    return mkMessageStringCore msg.severity msg.fileName msg.caption s msg.pos endPos? infoWithPos
  | .error e =>
    return mkMessageStringCore .error msg.fileName msg.caption (toString e) msg.pos endPos? infoWithPos

def mkLogString (log : MessageLog) : BaseIO String :=
  log.toList.foldlM (init := "") fun s m => do
    return s ++ (← mkMessageString m (infoWithPos := true))

def testInvalid (tomlFile : FilePath) : BaseIO TestOutcome := do
  match (← parseToml tomlFile) with
  | .pass t => return .fail (ppTable t)
  | .fail l => return .pass (← mkLogString l)
  | .error e => return .error (toString e)

local instance [Monad m] : ForIn m (RBNode α β) ((a : α) × β a) where
  forIn t init f := t.forIn init (fun a b acc => f ⟨a, b⟩ acc)

def expectBEq [BEq α] [ToString α] (actual expected : α) : Except String Unit := do
  unless actual == expected do
    throw s!"expected '{expected}', got '{actual}'"

def expectPrimitive (actualTy : String) (expected : Json) : Except String String := do
  let .ok expected := expected.getObj?
    | throw s!"expected non-primitive, got '{actualTy}'"
  let some ty := expected.find compare "type"
    | throw s!"expected non-primitive, got '{actualTy}'"
  let some val := expected.find compare "value"
    | throw s!"expected non-primitive, got '{actualTy}'"
  let .ok val := val.getStr?
    | throw s!"expected non-primitive, got '{actualTy}'"
  unless actualTy == ty do
    throw s!"expected value of type '{ty}', got '{actualTy}'"
  return val

mutual

partial def expectValue (actual : Value) (expected : Json) : Except String Unit := do
  match actual with
  | .boolean b => expectBEq (toString b) (← expectPrimitive "bool" expected)
  | .string s => expectBEq s (← expectPrimitive "string" expected)
  | .integer n => expectBEq (toString n) (← expectPrimitive "integer" expected)
  | .float actN =>
    let expected ← expectPrimitive "float" expected
    if expected.toLower == "nan" then
      unless actN.isNaN do
        throw s!"expected NaN, got '{actN}'"
    else
      expectBEq actN <| decodeFloat expected
  | .dateTime dt =>
    match dt with
    | .offsetDateTime _ _ _ => expectBEq (toString dt) (← expectPrimitive "datetime" expected)
    | .localDateTime .. =>  expectBEq (toString dt) (← expectPrimitive "datetime-local" expected)
    | .localDate d => expectBEq (toString d) (← expectPrimitive "date-local" expected)
    | .localTime t => expectBEq (toString t) (← expectPrimitive "time-local" expected)
  | .array actVs =>
    let .ok expVs := expected.getArr?
      | throw "expected non-array, got array"
    if h_size : actVs.size = expVs.size then
      Fin.forM actVs.size fun i => expectValue actVs[i] (expVs[i]'(h_size ▸ i.isLt))
    else
      throw s!"expected array of size {expVs.size}, got {actVs.size}:\n{actual}"
  | .table t => expectTable t expected

partial def expectTable (actual : Table) (expected : Json) : Except String Unit := do
  let .ok expected := expected.getObj?
    | throw "expected non-table, got table"
  if actual.size != expected.size then
    throw s!"expected table of size {expected.size}, got {actual.size}:\n{ppTable actual}"
  for ⟨k,expV⟩ in expected do
    let some actV := actual.find? k
      | throw s!"expected key '{k}'"
    try expectValue actV expV catch e => throw s!"{k}: {e}"

end

def expectJson (actual expected : Json) : TestOutcome :=
  let s := actual.pretty ++ "\n"
  if actual == expected then .pass s else .fail s

def testValid (tomlFile : FilePath) : BaseIO TestOutcome := do
  -- Tests skipped due to bugs in Lean's JSON parser
  -- TODO: Fix JSON parser (high-low unicode escape pairs)
  let normPath := tomlFile.toString.map fun c => if c = '\\' then '/' else c
  for testPath in ["string/quoted-unicode.toml", "key/quoted-unicode.toml"] do
    if normPath.endsWith testPath then return .skip
  match (← parseToml tomlFile) with
  | .pass t =>
    match (← IO.FS.readFile (tomlFile.withExtension "json") |>.toBaseIO) with
    | .ok contents =>
      match Json.parse contents with
      | .ok j =>
        match expectTable t j with
        | .ok _ => return .pass <| ppTable t
        | .error e => return .fail <| e.trimRight ++ "\n"
      | .error e => return .error s!"invalid JSON: {e}"
    | .error e => return .error (toString e)
  | .fail l => return .fail (← mkLogString l)
  | .error e => return .error (toString e)

def walkDir (root : FilePath) (ext : String := "toml") : IO (Array FilePath) := do
  (← root.walkDir).filterM fun path => do
    return path.extension == some ext && !(← path.isDir)

def main : IO UInt32 := do
  -- Detect Tests
  let invalidTestFiles ← walkDir <| FilePath.mk "tests" / "invalid"
  let validTestFiles ← walkDir <| FilePath.mk "tests" / "valid"
  let numTests := invalidTestFiles.size + validTestFiles.size
  let outcomes := Array.mkEmpty numTests
  -- Run Tests
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
    | .error s => errored := errored + 1; IO.print s!"{testName} errored:\n{s}\n"
  let percent := (numTests - skipped - failed - errored) * 100 / numTests
  IO.println s!"{percent}% of tests passed, {failed} failed, {errored} errored, {skipped} skipped out of {numTests}"
  return if failed > 0 || errored > 0 then 1 else 0

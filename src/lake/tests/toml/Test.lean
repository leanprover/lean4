import Lake.Toml

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

@[inline] def allLt (m : Nat) (f : (n : Nat) → n < m → Bool)  : Bool :=
  let rec @[specialize] loop : (n : Nat) → n ≤ m → Bool
    | 0      , _ => true
    | .succ n, h => f n (Nat.lt_of_succ_le h) && loop n (Nat.le_of_succ_le h)
  loop m (Nat.le_refl _)

def bytesBEq (a b : ByteArray) : Bool :=
  if h_size : a.size = b.size then
    allLt a.size fun i h => a[i] = b[i]'(h_size ▸ h)
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

def testValid (tomlFile : FilePath) : BaseIO TestOutcome := do
  match (← parseToml tomlFile) with
  | .pass _ => return .skip
  | .fail l => return .fail (← mkLogString l)
  | .error e => return .error (toString e)

def walkDir (root : FilePath) (ext : String := "toml") : IO (Array FilePath) := do
  (← root.walkDir).filterM fun path => do
    return path.extension == some ext && !(← path.isDir)

def main : IO Unit := do
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

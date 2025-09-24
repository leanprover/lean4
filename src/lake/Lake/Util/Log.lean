/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO
public import Init.Data.Repr
public import Init.Data.Ord.Basic
public import Lean.Data.Json
public import Lake.Util.Error
public import Lake.Util.EStateT
public import Lean.Message
public import Lake.Util.Lift

open Lean

namespace Lake

public inductive Verbosity
| quiet
| normal
| verbose
deriving Repr, DecidableEq, Ord

public instance : LT Verbosity := ltOfOrd
public instance : LE Verbosity := leOfOrd
public instance : Min Verbosity := minOfLe
public instance : Max Verbosity := maxOfLe

public instance : Inhabited Verbosity := ⟨.normal⟩

/-- Whether to ANSI escape codes. -/
public inductive AnsiMode
/--
Automatically determine whether to use ANSI escape codes
based on whether the stream written to is a terminal.
-/
| auto
/-- Use ANSI escape codes. -/
| ansi
/-- Do not use ANSI escape codes. -/
| noAnsi
deriving Repr

/-- Returns whether to ANSI escape codes with the stream `out`. -/
public def AnsiMode.isEnabled (out : IO.FS.Stream) : AnsiMode → BaseIO Bool
| .auto => out.isTty
| .ansi => pure true
| .noAnsi => pure false

/--
Wrap text in ANSI escape sequences to make it bold and color it the ANSI `colorCode`.
Resets all terminal font attributes at the end of the text.
-/
public def Ansi.chalk (colorCode text : String) : String :=
  s!"\x1B[1;{colorCode}m{text}\x1B[m"

/-- A pure representation of output stream. -/
public inductive OutStream
| stdout
| stderr
| stream (s : IO.FS.Stream)

/-- Returns the real output stream associated with `OutStream`. -/
public def OutStream.get : OutStream → BaseIO IO.FS.Stream
| .stdout => IO.getStdout
| .stderr => IO.getStderr
| .stream s => pure s

public instance : Coe IO.FS.Stream OutStream := ⟨.stream⟩
public instance : Coe IO.FS.Handle OutStream := ⟨fun h => .stream (.ofHandle h)⟩

public inductive LogLevel
| trace
| info
| warning
| error
deriving Inhabited, Repr, DecidableEq, Ord, ToJson, FromJson

public instance : LT LogLevel := ltOfOrd
public instance : LE LogLevel := leOfOrd
public instance : Min LogLevel := minOfLe
public instance : Max LogLevel := maxOfLe

/-- Unicode icon for representing the log level. -/
public def LogLevel.icon : LogLevel → Char
| .trace | .info => 'ℹ'
| .warning => '⚠'
| .error => '✖'

/-- ANSI escape code for coloring text of at the log level. -/
public def LogLevel.ansiColor : LogLevel → String
| .trace | .info => "34"
| .warning => "33"
| .error => "31"

public def LogLevel.ofString? (s : String) : Option LogLevel :=
  match s.toLower with
  | "trace" => some .trace
  | "info" | "information" => some .info
  | "warn" | "warning" => some .warning
  | "error" => some .error
  | _ => none

public protected def LogLevel.toString : LogLevel → String
| .trace => "trace"
| .info => "info"
| .warning => "warning"
| .error => "error"

instance : ToString LogLevel := ⟨LogLevel.toString⟩

public def LogLevel.ofMessageSeverity : MessageSeverity → LogLevel
| .information => .info
| .warning => .warning
| .error => .error

public def LogLevel.toMessageSeverity : LogLevel → MessageSeverity
| .info | .trace => .information
| .warning => .warning
| .error => .error

public def Verbosity.minLogLv : Verbosity → LogLevel
| .quiet => .warning
| .normal =>  .info
| .verbose => .trace

public structure LogEntry where
  level : LogLevel
  message : String
  deriving Inhabited, ToJson, FromJson

public protected def LogEntry.toString (self : LogEntry) (useAnsi := false) : String :=
  if useAnsi then
    let {level := lv, message := msg} := self
    let pre := Ansi.chalk lv.ansiColor s!"{lv.toString}:"
    s!"{pre} {msg}"
  else
    s!"{self.level}: {self.message}"

public instance : ToString LogEntry := ⟨LogEntry.toString⟩

@[inline] public def LogEntry.trace (message : String) : LogEntry :=
  {level := .trace, message}

@[inline] public def LogEntry.info (message : String) : LogEntry :=
  {level := .info, message}

@[inline] public def LogEntry.warning (message : String) : LogEntry :=
  {level := .warning, message}

@[inline] public def LogEntry.error (message : String) : LogEntry :=
  {level := .error, message}

public def LogEntry.ofSerialMessage (msg : SerialMessage) : LogEntry :=
  let str := if msg.caption.trim.isEmpty then
     msg.data.trim else s!"{msg.caption.trim}:\n{msg.data.trim}"
  {
    level := .ofMessageSeverity msg.severity
    message := mkErrorStringWithPos msg.fileName msg.pos str none
  }

public def LogEntry.ofMessage (msg : Message) : BaseIO LogEntry := do
  -- Remark: The inline here avoids a new message allocation when `msg` is shared
  return inline <| .ofSerialMessage (← msg.serialize)

public class MonadLog (m : Type u → Type v) where
  logEntry (e : LogEntry) : m PUnit

export MonadLog (logEntry)

@[inline] public def logVerbose [Monad m] [MonadLog m] (message : String) : m PUnit := do
  logEntry (.trace message)

@[inline] public def logInfo [Monad m] [MonadLog m] (message : String) : m PUnit := do
  logEntry (.info message)

@[inline] public def logWarning [MonadLog m] (message : String) : m PUnit :=
  logEntry (.warning message)

@[inline] public def logError [MonadLog m] (message : String) : m PUnit :=
  logEntry (.error message)

@[inline] public def logSerialMessage (msg : SerialMessage) [Monad m] [MonadLog m] : m PUnit := do
  unless msg.isSilent do
    logEntry (.ofSerialMessage msg)

@[inline] public def logMessage
  (msg : Message) [Monad m] [MonadLog m] [MonadLiftT BaseIO m]
: m PUnit := do
  unless msg.isSilent do
    logEntry (← LogEntry.ofMessage msg)

public def logToStream
  (e : LogEntry) (out : IO.FS.Stream) (minLv : LogLevel) (useAnsi : Bool)
: BaseIO PUnit := do
  if e.level ≥ minLv then
    out.putStrLn (e.toString useAnsi) |>.catchExceptions fun _ => pure ()

namespace MonadLog

public abbrev nop [Pure m] : MonadLog m where
  logEntry _  := pure ()

public instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

public abbrev lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  logEntry e := liftM <| self.logEntry e

public instance [MonadLift m n] [methods : MonadLog m] : MonadLog n := methods.lift

public abbrev stream [MonadLiftT BaseIO m]
  (out : IO.FS.Stream) (minLv := LogLevel.info) (useAnsi := false)
: MonadLog m where logEntry e := logToStream e out minLv useAnsi

@[inline] public def error [Alternative m] [MonadLog m] (msg : String) : m α :=
  logError msg *> failure

end MonadLog

public def OutStream.logEntry
  (self : OutStream) (e : LogEntry)
  (minLv : LogLevel := .info) (ansiMode := AnsiMode.auto)
: BaseIO PUnit := do
  let out ← self.get
  let useAnsi ← ansiMode.isEnabled out
  logToStream e out minLv useAnsi

public abbrev OutStream.logger [MonadLiftT BaseIO m]
  (out : OutStream) (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: MonadLog m where logEntry e := out.logEntry e minLv ansiMode

public abbrev MonadLog.stdout
  [MonadLiftT BaseIO m] (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: MonadLog m := OutStream.stdout.logger minLv ansiMode

public abbrev MonadLog.stderr
  [MonadLiftT BaseIO m] (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: MonadLog m := OutStream.stderr.logger minLv ansiMode

@[inline] public def OutStream.getLogger [MonadLiftT BaseIO m]
  (out : OutStream) (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: BaseIO (MonadLog m) := do
  let out ← out.get
  let useAnsi ← ansiMode.isEnabled out
  return .stream out minLv useAnsi

/-- A monad equipped with a `MonadLog` instance -/
public abbrev MonadLogT (m : Type u → Type v) (n : Type v → Type w) :=
  ReaderT (MonadLog m) n

namespace MonadLogT

public instance [Pure n] [Inhabited α] : Inhabited (MonadLogT m n α) :=
  ⟨fun _ => pure Inhabited.default⟩

public instance [Monad n] [MonadLiftT m n] : MonadLog (MonadLogT m n) where
  logEntry e := do (← read).logEntry e

@[inline] public def adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

@[inline] public def ignoreLog [Pure m] (self : MonadLogT m n α) : n α :=
  self MonadLog.nop

end MonadLogT

/- A Lake log. An `Array` of log entries. -/
public structure Log where
  entries : Array LogEntry
  deriving Inhabited

public instance : ToJson Log := ⟨(toJson ·.entries)⟩
public instance : FromJson Log := ⟨(Log.mk <$> fromJson? ·)⟩

/-- A position in a `Log` (i.e., an array index). Can be past the log's end. -/
public structure Log.Pos where
  val : Nat
  deriving Inhabited, DecidableEq

public instance : OfNat Log.Pos (nat_lit 0) := ⟨⟨0⟩⟩
public instance : Ord Log.Pos := ⟨(compare ·.val ·.val)⟩
public instance : LT Log.Pos := ⟨(·.val < ·.val)⟩
public instance : DecidableRel (LT.lt (α := Log.Pos)) :=
  inferInstanceAs (DecidableRel (α := Log.Pos) (β := Log.Pos) (·.val < ·.val))
public instance : LE Log.Pos := ⟨(·.val ≤ ·.val)⟩
public instance : DecidableRel (LE.le (α := Log.Pos)) :=
  inferInstanceAs (DecidableRel (α := Log.Pos) (β := Log.Pos) (·.val ≤ ·.val))
public instance : Min Log.Pos := minOfLe
public instance : Max Log.Pos := maxOfLe

namespace Log

@[inline] public def empty : Log :=
  .mk #[]

public instance : EmptyCollection Log := ⟨Log.empty⟩

@[inline] public def size (log : Log) : Nat :=
  log.entries.size

@[inline] public def isEmpty (log : Log) : Bool :=
  log.size = 0

@[inline] public def hasEntries (log : Log) : Bool :=
  log.size ≠ 0

@[inline] public def endPos (log : Log) : Log.Pos :=
  ⟨log.entries.size⟩

@[inline] public def push (log : Log) (e : LogEntry) : Log :=
  .mk <| log.entries.push e

@[inline] public def append (log : Log) (o : Log) : Log :=
  .mk <| log.entries.append o.entries

public instance : Append Log := ⟨Log.append⟩

/-- Takes log entries between `start` (inclusive) and `stop` (exclusive). -/
@[inline] public def extract (log : Log) (start stop : Log.Pos)  : Log :=
  .mk <| log.entries.extract start.val stop.val

/-- Removes log entries after `pos` (inclusive). -/
@[inline] public def dropFrom (log : Log) (pos : Log.Pos) : Log :=
  .mk <| log.entries.shrink pos.val

/-- Takes log entries before `pos` (exclusive). -/
@[inline] public def takeFrom (log : Log) (pos : Log.Pos) : Log :=
  log.extract pos log.endPos

/--
Splits the log into two from `pos`.
The first log is from the start to `pos` (exclusive),
and the second log is from `pos` (inclusive) to the end.
-/
@[inline] public def split (log : Log) (pos : Log.Pos) : Log × Log :=
  (log.dropFrom pos, log.takeFrom pos)

public def toString (log : Log) : String :=
  log.entries.foldl (· ++ ·.toString ++ "\n") ""

public instance : ToString Log := ⟨Log.toString⟩

@[inline] public def replay [Monad m] [logger : MonadLog m] (log : Log) : m PUnit :=
  log.entries.forM fun e => logger.logEntry e

@[inline] public def filter (f : LogEntry → Bool) (log : Log) : Log :=
  .mk <| log.entries.filter f

@[inline] public def any (f : LogEntry → Bool) (log : Log) : Bool :=
  log.entries.any f

/-- The max log level of entries in this log. If empty, returns `trace`. -/
public def maxLv (log : Log) : LogLevel :=
  log.entries.foldl (max · ·.level) .trace

end Log

/-- Add a `LogEntry` to the end of the monad's `Log`. -/
@[inline] public def pushLogEntry
  [MonadStateOf Log m] (e : LogEntry)
: m PUnit := modify (·.push e)

public abbrev MonadLog.ofMonadState [MonadStateOf Log m] : MonadLog m := ⟨pushLogEntry⟩

/-- Returns the monad's log. -/
@[inline] public def getLog [MonadStateOf Log m] : m Log :=
  get

/-- Returns the current end position of the monad's log (i.e., its size). -/
@[inline] public def getLogPos [Functor m] [MonadStateOf Log m] : m Log.Pos :=
  (·.endPos) <$> getLog

/-- Removes the section monad's log starting and returns it. -/
@[inline] public def takeLog [MonadStateOf Log m] : m Log :=
  modifyGet fun log => (log, {})

/--
Removes the monad's log starting at `pos` and returns it.
Useful for extracting logged errors after catching an error position
from an `ELogT` (e.g., `LogIO`).
-/
@[inline] public def takeLogFrom [MonadStateOf Log m] (pos : Log.Pos) : m Log :=
  modifyGet fun log => (log.takeFrom pos, log.dropFrom pos)

/--
Backtracks the monad's log to `pos`.
Useful for discarding logged errors after catching an error position
from an `ELogT` (e.g., `LogIO`).
-/
@[inline] public def dropLogFrom [MonadStateOf Log m] (pos : Log.Pos) : m PUnit :=
  modify (·.dropFrom pos)

/-- Returns the log from `x` while leaving it intact in the monad. -/
@[inline] public def extractLog [Monad m] [MonadStateOf Log m] (x : m PUnit) : m Log := do
  let iniPos ← getLogPos
  x
  let log ← getLog
  return log.takeFrom iniPos

/-- Returns the log from `x` and its result while leaving it intact in the monad. -/
@[inline] public def withExtractLog [Monad m] [MonadStateOf Log m] (x : m α) : m (α × Log) := do
  let iniPos ← getLogPos
  let a ← x
  let log ← getLog
  return (a, log.takeFrom iniPos)

/-- Performs `x` and backtracks any error to the log position before `x`. -/
@[inline] public def withLogErrorPos
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m] (self : m α)
: m α := do
  let iniPos ← getLogPos
  try self catch _ => throw iniPos

/-- Performs `x` and groups all logs generated into an error block. -/
@[inline] public def errorWithLog
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m] (self : m PUnit)
: m β := do
  let iniPos ← getLogPos
  try self catch _ => pure ()
  throw iniPos

/-- Captures IO in `x` into an informational log entry. -/
@[inline] public def withLoggedIO
  [Monad m] [MonadLiftT BaseIO m] [MonadLog m] [MonadFinally m] (x : m α)
: m α := do
  let (out, a) ← IO.FS.withIsolatedStreams x
  unless out.isEmpty do logInfo s!"stdout/stderr:\n{out.trim}"
  return a

/-- Throw with the logged error `message`. -/
@[inline] public protected def ELog.error
  [Monad m] [MonadLog m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
  (msg : String)
: m α := errorWithLog (logError msg)

/-- `MonadError` instance for monads with `Log` state and `Log.Pos` errors. -/
public abbrev ELog.monadError
  [Monad m] [MonadLog m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
: MonadError m := ⟨ELog.error⟩

/-- Fail without logging anything. -/
@[inline] public protected def ELog.failure
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
: m α := do throw (← getLogPos)

/-- Performs `x`. If it fails, drop its log and perform `y`. -/
@[inline] public protected def ELog.orElse
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
  (x : m α) (y : Unit → m α)
: m α := try x catch errPos => dropLogFrom errPos; y ()

/-- `Alternative` instance for monads with `Log` state and `Log.Pos` errors. -/
public abbrev ELog.alternative
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
: Alternative m where
  failure := ELog.failure
  orElse  := ELog.orElse

/-- A monad equipped with a log. -/
public abbrev LogT (m : Type → Type) :=
  StateT Log m

public instance [Monad m] : MonadLog (LogT m) := .ofMonadState

namespace LogT

public abbrev run [Functor m] (self : LogT m α) (log : Log := {})  : m (α × Log) :=
  StateT.run self log

public abbrev run' [Functor m] (self : LogT m α) (log : Log := {}) :  m α :=
  StateT.run' self log

/--
Run `self` with the log taken from the state of the monad `n`.

**Warning:** If lifting `self` from `m` to `n` fails, the log will be lost.
Thus, this is best used when the lift cannot fail.
-/
@[inline] public def takeAndRun
  [Monad n] [MonadStateOf Log n] [MonadLiftT m n] [MonadFinally n]
  (self : LogT m α)
: n α := do
  let (a, log) ← self (← takeLog)
  set log
  return a

/--
Runs `self` in `n` and then replays the entries of the resulting log
using the new monad's `logger`.
-/
@[inline] public def replayLog
  [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : LogT m α)
: n α := do
  let (a, log) ← self {}
  log.replay (logger := logger)
  return a

end LogT

/-- A monad equipped with a log and the ability to error at some log position. -/
public abbrev ELogT (m : Type → Type) :=
  EStateT Log.Pos Log m

public abbrev ELogResult (α) := EResult Log.Pos Log α

public instance [Monad m] : MonadLog (ELogT m) := .ofMonadState
public instance [Monad m] : MonadError (ELogT m) := ELog.monadError
public instance [Monad m] : Alternative (ELogT m) := ELog.alternative

namespace ELogT

public abbrev run (self : ELogT m α) (log : Log := {})  : m (ELogResult α) :=
  EStateT.run log self

public abbrev run' [Functor m] (self : ELogT m α) (log : Log := {}) :  m (Except Log.Pos α) :=
  EStateT.run' log self

public abbrev toLogT [Functor m] (self : ELogT m α) : LogT m (Except Log.Pos α) :=
  self.toStateT

public abbrev toLogT? [Functor m] (self : ELogT m α) : LogT m (Option α) :=
  self.toStateT?

public abbrev run? [Functor m] (self : ELogT m α) (log : Log := {}) : m (Option α × Log) :=
  EStateT.run? log self

public abbrev run?' [Functor m] (self : ELogT m α) (log : Log := {}) : m (Option α) :=
  EStateT.run?' log self

@[inline] public def catchLog [Monad m] (f : Log → LogT m α) (self : ELogT m α) : LogT m α := do
  self.catchExceptions fun errPos => do f (← takeLogFrom errPos)

/--
Run `self` with the log taken from the state of the monad `n`,

**Warning:** If lifting `self` from `m` to `n` fails, the log will be lost.
Thus, this is best used when the lift cannot fail. This excludes the
native log position failure of `ELogT`, which are lifted safely.
-/
@[inline] public def takeAndRun
  [Monad n] [MonadStateOf Log n] [MonadExceptOf Log.Pos n] [MonadLiftT m n]
  (self : ELogT m α)
: n α := do
  match (← self.run (← takeLog)) with
  | .ok a log => set log; return a
  | .error e log => set log; throw e

/--
Runs `self` in `n` and then replays the entries of the resulting log
using the new monad's `logger`. Translates an exception in this monad
to a `none` result.
-/
@[inline] public def replayLog?
  [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : ELogT m α)
: n (Option α) := do
  match (← self.run {}) with
  | .ok a log => log.replay (logger := logger) *> pure (some a)
  | .error _ log => log.replay (logger := logger) *> pure none

/--
Runs `self` in `n` and then replays the entries of the resulting log
using the new monad's `logger`. Translates an exception in this monad to
a `failure` in the new monad.
-/
@[inline] public def replayLog
  [Alternative n] [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : ELogT m α)
: n α := do
  match (← self.run {}) with
  | .ok a log => log.replay (logger := logger) *> pure a
  | .error _ log => log.replay (logger := logger) *> failure

end ELogT

/-- A monad equipped with a log, a log error position, and the ability to perform I/O. -/
public abbrev LogIO := ELogT BaseIO

public instance : MonadLift IO LogIO := ⟨MonadError.runIO⟩

namespace LogIO

/--
Runs a `LogIO` action in `BaseIO`.
Prints log entries of at least `minLv` to `out`.
-/
@[inline] public def toBaseIO (self : LogIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: BaseIO (Option α) := do
  let logger ← out.getLogger minLv ansiMode
  let (a?, log) ← self.run? {}
  replay log logger
  return a?
where
  -- avoid specialization of this call at each call site
  replay (log : Log) (logger : MonadLog BaseIO) : BaseIO Unit :=
    log.replay (logger := logger)

-- deprecated 2024-05-18, reversed 2024-10-18
public abbrev captureLog := @ELogT.run?

end LogIO

/--
A monad equipped with a log function and the ability to perform I/O.
Unlike `LogIO`, log entries are not retained by the monad but instead eagerly
passed to the log function.
-/
public abbrev LoggerIO := MonadLogT BaseIO (EIO PUnit)

public instance : MonadError LoggerIO := ⟨MonadLog.error⟩
public instance : MonadLift IO LoggerIO := ⟨MonadError.runIO⟩
public instance : MonadLift LogIO LoggerIO := ⟨ELogT.replayLog⟩

namespace LoggerIO

/--
Runs a `LoggerIO` action in `BaseIO`.
Prints log entries of at least `minLv` to `out`.
-/
@[inline] public def toBaseIO
  (self : LoggerIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: BaseIO (Option α) := do
  (·.toOption) <$> (self.run (← out.getLogger minLv ansiMode)).toBaseIO

public def captureLog (self : LoggerIO α) : BaseIO (Option α × Log) := do
  let ref ← IO.mkRef ({} : Log)
  let e ← self.run ⟨fun e => ref.modify (·.push e)⟩ |>.toBaseIO
  return (e.toOption, ← ref.get)

-- For parity with `LogIO.run?`
public abbrev run? := @captureLog

-- For parity with `LogIO.run?'`
@[inline] public def run?'
  (self : LoggerIO α) (logger : LogEntry → BaseIO PUnit := fun _ => pure ())
: BaseIO (Option α) := do
  (·.toOption) <$> (self.run ⟨logger⟩).toBaseIO

end LoggerIO

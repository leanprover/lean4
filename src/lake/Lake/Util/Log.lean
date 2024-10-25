/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Error
import Lake.Util.EStateT
import Lake.Util.Lift
import Lean.Data.Json
import Lean.Message

open Lean

namespace Lake

inductive Verbosity
| quiet
| normal
| verbose
deriving Repr, DecidableEq, Ord

instance : LT Verbosity := ltOfOrd
instance : LE Verbosity := leOfOrd
instance : Min Verbosity := minOfLe
instance : Max Verbosity := maxOfLe

instance : Inhabited Verbosity := ⟨.normal⟩

/-- Whether to ANSI escape codes. -/
inductive AnsiMode
/--
Automatically determine whether to use ANSI escape codes
based on whether the stream written to is a terminal.
-/
| auto
/-- Use ANSI escape codes. -/
| ansi
/-- Do not use ANSI escape codes. -/
| noAnsi

/-- Returns whether to ANSI escape codes with the stream `out`. -/
def AnsiMode.isEnabled (out : IO.FS.Stream) : AnsiMode → BaseIO Bool
| .auto => out.isTty
| .ansi => pure true
| .noAnsi => pure false

/--
Wrap text in ANSI escape sequences to make it bold and color it the ANSI `colorCode`.
Resets all terminal font attributes at the end of the text.
-/
def Ansi.chalk (colorCode text : String) : String :=
  s!"\x1B[1;{colorCode}m{text}\x1B[m"

/-- A pure representation of output stream. -/
inductive OutStream
| stdout
| stderr
| stream (s : IO.FS.Stream)

/-- Returns the real output stream associated with `OutStream`. -/
def OutStream.get : OutStream → BaseIO IO.FS.Stream
| .stdout => IO.getStdout
| .stderr => IO.getStderr
| .stream s => pure s

instance : Coe IO.FS.Stream OutStream := ⟨.stream⟩
instance : Coe IO.FS.Handle OutStream := ⟨fun h => .stream (.ofHandle h)⟩

inductive LogLevel
| trace
| info
| warning
| error
deriving Inhabited, Repr, DecidableEq, Ord, ToJson, FromJson

instance : LT LogLevel := ltOfOrd
instance : LE LogLevel := leOfOrd
instance : Min LogLevel := minOfLe
instance : Max LogLevel := maxOfLe

/-- Unicode icon for representing the log level. -/
def LogLevel.icon : LogLevel → Char
| .trace | .info => 'ℹ'
| .warning => '⚠'
| .error => '✖'

/-- ANSI escape code for coloring text of at the log level. -/
def LogLevel.ansiColor : LogLevel → String
| .trace | .info => "34"
| .warning => "33"
| .error => "31"

protected def LogLevel.ofString? (s : String) : Option LogLevel :=
  match s.toLower with
  | "trace" => some .trace
  | "info" | "information" => some .info
  | "warn" | "warning" => some .warning
  | "error" => some .error
  | _ => none

protected def LogLevel.toString : LogLevel → String
| .trace => "trace"
| .info => "info"
| .warning => "warning"
| .error => "error"

instance : ToString LogLevel := ⟨LogLevel.toString⟩

protected def LogLevel.ofMessageSeverity : MessageSeverity → LogLevel
| .information => .info
| .warning => .warning
| .error => .error

protected def LogLevel.toMessageSeverity : LogLevel → MessageSeverity
| .info | .trace => .information
| .warning => .warning
| .error => .error

def Verbosity.minLogLv : Verbosity → LogLevel
| .quiet => .warning
| .normal =>  .info
| .verbose => .trace

structure LogEntry where
  level : LogLevel
  message : String
  deriving Inhabited, ToJson, FromJson

protected def LogEntry.toString (self : LogEntry) (useAnsi := false) : String :=
  if useAnsi then
    let {level := lv, message := msg} := self
    let pre := Ansi.chalk lv.ansiColor s!"{lv.toString}:"
    s!"{pre} {msg.trim}"
  else
    s!"{self.level}: {self.message.trim}"

instance : ToString LogEntry := ⟨LogEntry.toString⟩

class MonadLog (m : Type u → Type v) where
  logEntry (e : LogEntry) : m PUnit

export MonadLog (logEntry)

@[inline] def logVerbose [Monad m] [MonadLog m] (message : String) : m PUnit := do
  logEntry {level := .trace, message}

@[inline] def logInfo [Monad m] [MonadLog m] (message : String) : m PUnit := do
  logEntry {level := .info, message}

@[inline] def logWarning [MonadLog m] (message : String) : m PUnit :=
  logEntry {level := .warning, message}

@[inline] def logError  [MonadLog m] (message : String) : m PUnit :=
  logEntry {level := .error, message}

@[specialize] def logSerialMessage (msg : SerialMessage) [MonadLog m] : m PUnit :=
  let str := if msg.caption.trim.isEmpty then
     msg.data.trim else s!"{msg.caption.trim}:\n{msg.data.trim}"
  logEntry {
    level := .ofMessageSeverity msg.severity
    message := mkErrorStringWithPos msg.fileName msg.pos str none
  }

@[deprecated (since := "2024-05-18")] def logToIO (e : LogEntry) (minLv : LogLevel)  : BaseIO PUnit := do
  match e.level with
  | .trace => if minLv ≥ .trace then
    IO.println e.message.trim |>.catchExceptions fun _ => pure ()
  | .info => if minLv ≥ .info then
    IO.println e.message.trim |>.catchExceptions fun _ => pure ()
  | .warning => IO.eprintln e.toString |>.catchExceptions fun _ => pure ()
  | .error => IO.eprintln e.toString |>.catchExceptions fun _ => pure ()

def logToStream
  (e : LogEntry) (out : IO.FS.Stream) (minLv : LogLevel) (useAnsi : Bool)
: BaseIO PUnit := do
  if e.level ≥ minLv then
    out.putStrLn (e.toString useAnsi) |>.catchExceptions fun _ => pure ()

namespace MonadLog

abbrev nop [Pure m] : MonadLog m where
  logEntry _  := pure ()

instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

abbrev lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  logEntry e := liftM <| self.logEntry e

instance [MonadLift m n] [methods : MonadLog m] : MonadLog n := methods.lift

set_option linter.deprecated false in
@[deprecated (since := "2024-05-18")] abbrev io [MonadLiftT BaseIO m] (minLv := LogLevel.info) : MonadLog m where
  logEntry e := logToIO e minLv

abbrev stream [MonadLiftT BaseIO m]
  (out : IO.FS.Stream) (minLv := LogLevel.info) (useAnsi := false)
: MonadLog m where logEntry e := logToStream e out minLv useAnsi

@[inline] def error [Alternative m] [MonadLog m] (msg : String) : m α :=
  logError msg *> failure

end MonadLog

def OutStream.logEntry
  (self : OutStream) (e : LogEntry)
  (minLv : LogLevel := .info) (ansiMode := AnsiMode.auto)
: BaseIO PUnit := do
  let out ← self.get
  let useAnsi ← ansiMode.isEnabled out
  logToStream e out minLv useAnsi

abbrev OutStream.logger [MonadLiftT BaseIO m]
  (out : OutStream) (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: MonadLog m where logEntry e := out.logEntry e minLv ansiMode

abbrev MonadLog.stdout
  [MonadLiftT BaseIO m] (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: MonadLog m := OutStream.stdout.logger minLv ansiMode

abbrev MonadLog.stderr
  [MonadLiftT BaseIO m] (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: MonadLog m := OutStream.stderr.logger minLv ansiMode

@[inline] def OutStream.getLogger [MonadLiftT BaseIO m]
  (out : OutStream) (minLv := LogLevel.info) (ansiMode := AnsiMode.auto)
: BaseIO (MonadLog m) := do
  let out ← out.get
  let useAnsi ← ansiMode.isEnabled out
  return .stream out minLv useAnsi

/-- A monad equipped with a `MonadLog` instance -/
abbrev MonadLogT (m : Type u → Type v) (n : Type v → Type w) :=
  ReaderT (MonadLog m) n

namespace MonadLogT

instance [Pure n] [Inhabited α] : Inhabited (MonadLogT m n α) :=
  ⟨fun _ => pure Inhabited.default⟩

instance [Monad n] [MonadLiftT m n] : MonadLog (MonadLogT m n) where
  logEntry e := do (← read).logEntry e

@[inline] def adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

@[inline] def ignoreLog [Pure m] (self : MonadLogT m n α) : n α :=
  self MonadLog.nop

end MonadLogT

/- A Lake log. An `Array` of log entries. -/
structure Log where
  entries : Array LogEntry

instance : ToJson Log := ⟨(toJson ·.entries)⟩
instance : FromJson Log := ⟨(Log.mk <$> fromJson? ·)⟩

/-- A position in a `Log` (i.e., an array index). Can be past the log's end. -/
structure Log.Pos where
  val : Nat
  deriving Inhabited

instance : OfNat Log.Pos (nat_lit 0) := ⟨⟨0⟩⟩

namespace Log

@[inline] def empty : Log :=
  .mk #[]

instance : EmptyCollection Log := ⟨Log.empty⟩

@[inline] def size (log : Log) : Nat :=
  log.entries.size

@[inline] def isEmpty (log : Log) : Bool :=
  log.size = 0

@[inline] def hasEntries (log : Log) : Bool :=
  log.size ≠ 0

@[inline] def endPos (log : Log) : Log.Pos :=
  ⟨log.entries.size⟩

@[inline] def push (log : Log) (e : LogEntry) : Log :=
  .mk <| log.entries.push e

@[inline] def append (log : Log) (o : Log) : Log :=
  .mk <| log.entries.append o.entries

instance : Append Log := ⟨Log.append⟩

/-- Takes log entries between `start` (inclusive) and `stop` (exclusive). -/
@[inline] def extract (log : Log) (start stop : Log.Pos)  : Log :=
  .mk <| log.entries.extract start.val stop.val

/-- Removes log entries after `pos` (inclusive). -/
@[inline] def dropFrom (log : Log) (pos : Log.Pos) : Log :=
  .mk <| log.entries.take pos.val

/-- Takes log entries before `pos` (exclusive). -/
@[inline] def takeFrom (log : Log) (pos : Log.Pos) : Log :=
  log.extract pos log.endPos

/--
Splits the log into two from `pos`.
The first log is from the start to `pos` (exclusive),
and the second log is from `pos` (inclusive) to the end.
-/
@[inline] def split (log : Log) (pos : Log.Pos) : Log × Log :=
  (log.dropFrom pos, log.takeFrom pos)

def toString (log : Log) : String :=
  log.entries.foldl (· ++ ·.toString ++ "\n") ""

instance : ToString Log := ⟨Log.toString⟩

@[inline] def replay [Monad m] [logger : MonadLog m] (log : Log) : m PUnit :=
  log.entries.forM fun e => logger.logEntry e

@[inline] def filter (f : LogEntry → Bool) (log : Log) : Log :=
  .mk <| log.entries.filter f

@[inline] def any (f : LogEntry → Bool) (log : Log) : Bool :=
  log.entries.any f

/-- The max log level of entries in this log. If empty, returns `trace`. -/
def maxLv (log : Log) : LogLevel :=
  log.entries.foldl (max · ·.level) .trace

end Log

/-- Add a `LogEntry` to the end of the monad's `Log`. -/
@[inline] def pushLogEntry
  [MonadStateOf Log m] (e : LogEntry)
: m PUnit := modify (·.push e)

abbrev MonadLog.ofMonadState [MonadStateOf Log m] : MonadLog m := ⟨pushLogEntry⟩

/-- Returns the monad's log. -/
@[inline] def getLog [MonadStateOf Log m] : m Log :=
  get

/-- Returns the current end position of the monad's log (i.e., its size). -/
@[inline] def getLogPos [Functor m] [MonadStateOf Log m] : m Log.Pos :=
  (·.endPos) <$> getLog

/-- Removes the section monad's log starting and returns it. -/
@[inline] def takeLog [MonadStateOf Log m] : m Log :=
  modifyGet fun log => (log, {})

/--
Removes the monad's log starting at `pos` and returns it.
Useful for extracting logged errors after catching an error position
from an `ELogT` (e.g., `LogIO`).
-/
@[inline] def takeLogFrom [MonadStateOf Log m] (pos : Log.Pos) : m Log :=
  modifyGet fun log => (log.takeFrom pos, log.dropFrom pos)

/--
Backtracks the monad's log to `pos`.
Useful for discarding logged errors after catching an error position
from an `ELogT` (e.g., `LogIO`).
-/
@[inline] def dropLogFrom [MonadStateOf Log m] (pos : Log.Pos) : m PUnit :=
  modify (·.dropFrom pos)

/-- Returns the log from `x` while leaving it intact in the monad. -/
@[inline] def extractLog [Monad m] [MonadStateOf Log m] (x : m PUnit) : m Log := do
  let iniPos ← getLogPos
  x
  let log ← getLog
  return log.takeFrom iniPos

/-- Returns the log from `x` and its result while leaving it intact in the monad. -/
@[inline] def withExtractLog [Monad m] [MonadStateOf Log m] (x : m α) : m (α × Log) := do
  let iniPos ← getLogPos
  let a ← x
  let log ← getLog
  return (a, log.takeFrom iniPos)

/-- Performs `x` and backtracks any error to the log position before `x`. -/
@[inline] def withLogErrorPos
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m] (self : m α)
: m α := do
  let iniPos ← getLogPos
  try self catch _ => throw iniPos

/-- Performs `x` and groups all logs generated into an error block. -/
@[inline] def errorWithLog
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m] (self : m PUnit)
: m β := do
  let iniPos ← getLogPos
  try self catch _ => pure ()
  throw iniPos

/-- Captures IO in `x` into an informational log entry. -/
@[inline] def withLoggedIO
  [Monad m] [MonadLiftT BaseIO m] [MonadLog m] [MonadFinally m] (x : m α)
: m α := do
  let (out, a) ← IO.FS.withIsolatedStreams x
  unless out.isEmpty do logInfo s!"stdout/stderr:\n{out}"
  return a

/-- Throw with the logged error `message`. -/
@[inline] protected def ELog.error
  [Monad m] [MonadLog m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
  (msg : String)
: m α := errorWithLog (logError msg)

/-- `MonadError` instance for monads with `Log` state and `Log.Pos` errors. -/
abbrev ELog.monadError
  [Monad m] [MonadLog m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
: MonadError m := ⟨ELog.error⟩

/-- Fail without logging anything. -/
@[inline] protected def ELog.failure
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
: m α := do throw (← getLogPos)

/-- Performs `x`. If it fails, drop its log and perform `y`. -/
@[inline] protected def ELog.orElse
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
  (x : m α) (y : Unit → m α)
: m α := try x catch errPos => dropLogFrom errPos; y ()

/-- `Alternative` instance for monads with `Log` state and `Log.Pos` errors. -/
abbrev ELog.alternative
  [Monad m] [MonadStateOf Log m] [MonadExceptOf Log.Pos m]
: Alternative m where
  failure := ELog.failure
  orElse  := ELog.orElse

/-- A monad equipped with a log. -/
abbrev LogT (m : Type → Type) :=
  StateT Log m

instance [Monad m] : MonadLog (LogT m) := .ofMonadState

namespace LogT

abbrev run [Functor m] (self : LogT m α) (log : Log := {})  : m (α × Log) :=
  StateT.run self log

abbrev run' [Functor m] (self : LogT m α) (log : Log := {}) :  m α :=
  StateT.run' self log

/--
Run `self` with the log taken from the state of the monad `n`.

**Warning:** If lifting `self` from `m` to `n` fails, the log will be lost.
Thus, this is best used when the lift cannot fail.
-/
@[inline] def takeAndRun
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
@[inline] def replayLog [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : LogT m α) : n α := do
  let (a, log) ← self {}
  log.replay (logger := logger)
  return a

end LogT

/-- A monad equipped with a log and the ability to error at some log position. -/
abbrev ELogT (m : Type → Type) :=
  EStateT Log.Pos Log m

abbrev ELogResult (α) := EResult Log.Pos Log α

instance [Monad m] : MonadLog (ELogT m) := .ofMonadState
instance [Monad m] : MonadError (ELogT m) := ELog.monadError
instance [Monad m] : Alternative (ELogT m) := ELog.alternative

namespace ELogT

abbrev run (self : ELogT m α) (log : Log := {})  : m (ELogResult α) :=
  EStateT.run log self

abbrev run' [Functor m] (self : ELogT m α) (log : Log := {}) :  m (Except Log.Pos α) :=
  EStateT.run' log self

abbrev toLogT [Functor m] (self : ELogT m α) : LogT m (Except Log.Pos α) :=
  self.toStateT

abbrev toLogT? [Functor m] (self : ELogT m α) : LogT m (Option α) :=
  self.toStateT?

abbrev run? [Functor m] (self : ELogT m α) (log : Log := {}) : m (Option α × Log) :=
  EStateT.run? log self

abbrev run?' [Functor m] (self : ELogT m α) (log : Log := {}) : m (Option α) :=
  EStateT.run?' log self

@[inline] def catchLog [Monad m] (f : Log → LogT m α) (self : ELogT m α) : LogT m α := do
  self.catchExceptions fun errPos => do f (← takeLogFrom errPos)

@[deprecated run? (since := "2024-05-18")] abbrev captureLog := @run?

/--
Run `self` with the log taken from the state of the monad `n`,

**Warning:** If lifting `self` from `m` to `n` fails, the log will be lost.
Thus, this is best used when the lift cannot fail. This excludes the
native log position failure of `ELogT`, which are lifted safely.
-/
@[inline] def takeAndRun
  [Monad n] [MonadStateOf Log n] [MonadExceptOf Log.Pos n] [MonadLiftT m n]
  (self : ELogT m α)
: n α := do
  match (← self (← takeLog)) with
  | .ok a log => set log; return a
  | .error e log => set log; throw e

/--
Runs `self` in `n` and then replays the entries of the resulting log
using the new monad's `logger`. Translates an exception in this monad
to a `none` result.
-/
@[inline] def replayLog? [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : ELogT m α) : n (Option α) := do
  match (← self {}) with
  | .ok a log => log.replay (logger := logger) *> pure (some a)
  | .error _ log => log.replay (logger := logger) *> pure none

/--
Runs `self` in `n` and then replays the entries of the resulting log
using the new monad's `logger`. Translates an exception in this monad to
a `failure` in the new monad.
-/
@[inline] def replayLog [Alternative n] [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : ELogT m α) : n α := do
  match (← self {}) with
  | .ok a log => log.replay (logger := logger) *> pure a
  | .error _ log => log.replay (logger := logger) *> failure

end ELogT

/-- A monad equipped with a log, a log error position, and the ability to perform I/O. -/
abbrev LogIO := ELogT BaseIO

instance : MonadLift IO LogIO := ⟨MonadError.runIO⟩

namespace LogIO

/--
Runs a `LogIO` action in `BaseIO`.
Prints log entries of at least `minLv` to `out`.
-/
@[inline] def toBaseIO (self : LogIO α)
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
abbrev captureLog := @ELogT.run?

end LogIO

/--
A monad equipped with a log function and the ability to perform I/O.
Unlike `LogIO`, log entries are not retained by the monad but instead eagerly
passed to the log function.
-/
abbrev LoggerIO := MonadLogT BaseIO (EIO PUnit)

instance : MonadError LoggerIO := ⟨MonadLog.error⟩
instance : MonadLift IO LoggerIO := ⟨MonadError.runIO⟩
instance : MonadLift LogIO LoggerIO := ⟨ELogT.replayLog⟩

namespace LoggerIO

/--
Runs a `LoggerIO` action in `BaseIO`.
Prints log entries of at least `minLv` to `out`.
-/
@[inline] def toBaseIO
  (self : LoggerIO α)
  (minLv := LogLevel.info) (ansiMode := AnsiMode.auto) (out := OutStream.stderr)
: BaseIO (Option α) := do
  (·.toOption) <$> (self.run (← out.getLogger minLv ansiMode)).toBaseIO

def captureLog (self : LoggerIO α) : BaseIO (Option α × Log) := do
  let ref ← IO.mkRef ({} : Log)
  let e ← self.run ⟨fun e => ref.modify (·.push e)⟩ |>.toBaseIO
  return (e.toOption, ← ref.get)

-- For parity with `LogIO.run?`
abbrev run? := @captureLog

-- For parity with `LogIO.run?'`
@[inline] def run?'
  (self : LoggerIO α) (logger : LogEntry → BaseIO PUnit := fun _ => pure ())
: BaseIO (Option α) := do
  (·.toOption) <$> (self.run ⟨logger⟩).toBaseIO

end LoggerIO

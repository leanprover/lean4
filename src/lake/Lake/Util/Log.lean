/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Error
import Lake.Util.EStateT
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

protected def LogLevel.toString : LogLevel → String
| .trace => "trace"
| .info => "info"
| .warning => "warning"
| .error => "error"

protected def LogLevel.ofMessageSeverity : MessageSeverity → LogLevel
| .information => .info
| .warning => .warning
| .error => .error

instance : ToString LogLevel := ⟨LogLevel.toString⟩

def LogLevel.visibleAtVerbosity (self : LogLevel) (verbosity : Verbosity) : Bool :=
  match self with
  | .trace => verbosity == .verbose
  | .info => verbosity != .quiet
  | _ => true

structure LogEntry where
  level : LogLevel
  message : String
  deriving Inhabited, ToJson, FromJson

protected def LogEntry.toString (self : LogEntry) : String :=
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

def logToIO (e : LogEntry) (verbosity : Verbosity) : BaseIO PUnit := do
  match e.level with
  | .trace => if verbosity == .verbose then
    IO.println e.message.trim |>.catchExceptions fun _ => pure ()
  | .info => if verbosity != .quiet then
    IO.println e.message.trim |>.catchExceptions fun _ => pure ()
  | .warning => IO.eprintln s!"warning: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .error => IO.eprintln s!"error: {e.message.trim}" |>.catchExceptions fun _ => pure ()

def logToStream (e : LogEntry) (h : IO.FS.Stream) (verbosity : Verbosity) : BaseIO PUnit := do
  match e.level with
  | .trace => if verbosity == .verbose then
    h.putStrLn s!"trace: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .info => if verbosity != .quiet then
    h.putStrLn s!"info: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .warning => h.putStrLn s!"warning: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .error => h.putStrLn s!"error: {e.message.trim}" |>.catchExceptions fun _ => pure ()

@[specialize] def logSerialMessage (msg : SerialMessage) [MonadLog m] : m PUnit :=
  let str := msg.data
  let str := if msg.caption.trim.isEmpty then
    str.trim else s!"{msg.caption.trim}:\n{str.trim}"
  logEntry {
    level := .ofMessageSeverity msg.severity
    message := mkErrorStringWithPos msg.fileName msg.pos str msg.endPos
  }

namespace MonadLog

@[specialize] def nop [Pure m] : MonadLog m :=
  ⟨fun _ => pure ()⟩

instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

@[specialize] def io [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := logToIO e verbosity

@[inline] def stream [MonadLiftT BaseIO m] (h : IO.FS.Stream) (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := logToStream e h verbosity

@[inline] def stdout [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := liftM (m := BaseIO) do logToStream e (← IO.getStdout) verbosity

@[inline] def stderr [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := liftM (m := BaseIO) do logToStream e (← IO.getStderr) verbosity

@[inline] def lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  logEntry e := liftM <| self.logEntry e

instance [MonadLift m n] [methods : MonadLog m] : MonadLog n := lift methods

end MonadLog

abbrev MonadLogT (m : Type u → Type v) (n : Type v → Type w) :=
  ReaderT (MonadLog m) n

instance [Pure n] [Inhabited α] : Inhabited (MonadLogT m n α) :=
  ⟨fun _ => pure Inhabited.default⟩

instance [Monad n] [MonadLiftT m n] : MonadLog (MonadLogT m n) where
  logEntry e := do (← read).logEntry e

@[inline] def MonadLogT.adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

@[inline] def  MonadLogT.ignoreLog [Pure m] (self : MonadLogT m n α) : n α :=
  self MonadLog.nop

/- A Lake log. An `Array` of log entries. -/
structure Log where
  entries : Array LogEntry

instance : ToJson Log := ⟨(toJson ·.entries)⟩
instance : FromJson Log := ⟨(Log.mk <$> fromJson? ·)⟩

/-- A position in a `Log` (i.e., an array index). Can be past the log's end. -/
structure Log.Pos where
  val : Nat

instance : OfNat Log.Pos (nat_lit 0) := ⟨⟨0⟩⟩

namespace Log

@[inline] def empty : Log :=
  .mk #[]

instance : EmptyCollection Log := ⟨Log.empty⟩

@[inline] def isEmpty (log : Log) : Bool :=
  log.entries.isEmpty

@[inline] def size (log : Log) : Nat :=
  log.entries.size

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
  .mk <| log.entries.shrink pos.val

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

def filterByVerbosity (log : Log) (verbosity := Verbosity.normal) : Log :=
  log.filter (·.level.visibleAtVerbosity verbosity)

@[inline] def any (f : LogEntry → Bool) (log : Log) : Bool :=
  log.entries.any f

def hasVisibleEntries (log : Log) (verbosity := Verbosity.normal) : Bool :=
  log.any (·.level.visibleAtVerbosity verbosity)

end Log

/-- Returns the monad's log. -/
@[inline] def getLog [MonadStateOf Log m] : m Log :=
  get

/-- Returns the current end position of the monad's log (i.e., its size). -/
@[inline] def getLogPos [Functor m] [MonadStateOf Log m] : m Log.Pos :=
  (·.endPos) <$> getLog

/--
Backtracks the monad's log to `pos`.
Useful for discarding logged errors after catching an error position
from an `ELogT` (e.g., `LogIO`).
-/
@[inline] def dropLogFrom [MonadStateOf Log m] (pos : Log.Pos) : m PUnit :=
  modify (·.dropFrom pos)

/--
Removes the section monad's log starting at `pos` and returns it.
Useful for extracting logged errors after catching an error position
from an `ELogT` (e.g., `LogIO`).
-/
@[inline] def takeLogFrom [MonadStateOf Log m] (pos : Log.Pos) : m Log :=
  modifyGet fun log => (log.takeFrom pos, log.dropFrom pos)

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

/-- A monad equipped with a log. -/
abbrev LogT (m : Type → Type) :=
  StateT Log m

namespace LogT

@[inline] protected def log [Monad m] (e : LogEntry) : LogT m PUnit :=
  modify (·.push e)

instance [Monad m] : MonadLog (LogT m) := ⟨LogT.log⟩

@[inline] def replayLog [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : LogT m α) : n α := do
  let (a, log) ← self {}
  log.replay (logger := logger)
  return a

end LogT

/-- A monad equipped with a log and the ability to error at some log position. -/
abbrev ELogT (m : Type → Type) :=
  EStateT Log.Pos Log m

abbrev ELogResult (α) := EResult Log.Pos Log α

namespace ELogT

@[inline] protected def log [Monad m] (e : LogEntry) : ELogT m PUnit :=
  modify (·.push e)

instance [Monad m] : MonadLog (ELogT m) := ⟨ELogT.log⟩

@[inline] protected def error [Monad m] (msg : String) : ELogT m α :=
  errorWithLog (logError msg)

instance [Monad m] : MonadError (ELogT m) := ⟨ELogT.error⟩

/-- Fail without logging anything. -/
@[inline] protected def ELogT.failure [Monad m] : ELogT m α := do
  throw (← getLogPos)

/-- Performs `x`. If it fails, drop its log and perform `y`. -/
@[inline] protected def ELogT.orElse [Monad m] (x : ELogT m α) (y : Unit → ELogT m α)  : ELogT m α :=
  try x catch errPos => dropLogFrom errPos; y ()

instance [Monad m] : Alternative (ELogT m) where
  failure := ELogT.failure
  orElse  := ELogT.orElse

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

@[inline] def catchFailure [Monad m] (f : Log → LogT m α) (self : ELogT m α) : LogT m α := fun log => do
  match (← self log) with
  | .error n log => let (h,t) := log.split n; f h t
  | .ok a log => return (a, log)

@[inline] def captureLog [Monad m] (self : ELogT m α) : m (Option α × Log) := do
 match (← self {}) with
 | .ok a log => return (some a, log)
 | .error _ log => return (none, log)

end ELogT

abbrev LogIO := ELogT BaseIO

instance : MonadLift IO LogIO := ⟨MonadError.runIO⟩

/--
Runs a `LogIO` action in `BaseIO`.
Prints logs message at `verbosity` to stderr or stdout (if `useStdout`).
-/
@[inline] def LogIO.toBaseIO
  (x : LogIO α) (verbosity := Verbosity.normal) (useStdout := false)
: BaseIO (Option α) :=
  let logger := if useStdout then .stdout verbosity else .stderr verbosity
  x.replayLog? (logger := logger)

/-- Captures IO in `x` into an informational log entry. -/
@[inline] def withLoggedIO
  [Monad m] [MonadLiftT BaseIO m] [MonadLog m] [MonadFinally m] (x : m α)
: m α := do
  let (out, a) ← IO.FS.withIsolatedStreams x
  unless out.isEmpty do logInfo s!"stdout/stderr:\n{out}"
  return a

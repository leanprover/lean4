/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.UV.System
public import Std.Data.HashMap
import Init.Data.Ord.UInt

public section

open Std Time
open System

namespace Std
namespace Internal
namespace IO
namespace Process

/--
Represents resource usage statistics for a process or thread.
All time values are in milliseconds.
-/
structure ResourceUsageStats where
  /--
  CPU time spent in user mode (milliseconds)
  -/
  cpuUserTime : Time.Millisecond.Offset

  /--
  CPU time spent in kernel mode (milliseconds)
  -/
  cpuSystemTime : Time.Millisecond.Offset

  /--
  Peak resident set size (max physical memory usage) in kilobytes
  -/
  peakResidentSetSizeKb : UInt64

  /--
  Size of shared memory segments (kilobytes)
  -/
  sharedMemorySizeKb : UInt64

  /--
  Size of unshared data segment (kilobytes)
  -/
  unsharedDataSizeKb : UInt64

  /--
  Size of unshared stack segment (kilobytes)
  -/
  unsharedStackSizeKb : UInt64

  /--
  Number of minor (soft) page faults (no disk I/O)
  -/
  minorPageFaults : UInt64

  /--
  Number of major (hard) page faults (disk I/O required)
  -/
  majorPageFaults : UInt64

  /--
  Number of swap ins or swap outs
  -/
  swapOperations : UInt64

  /--
  Number of block input operations (disk reads)
  -/
  blockInputOps : UInt64

  /--
  Number of block output operations (disk writes)
  -/
  blockOutputOps : UInt64

  /--
  Number of IPC messages sent
  -/
  messagesSent : UInt64

  /--
  Number of IPC messages received
  -/
  messagesReceived : UInt64

  /--
  Number of signals received
  -/
  signalsReceived : UInt64

  /--
  Number of voluntary context switches (process yielded CPU)
  -/
  voluntaryContextSwitches : UInt64

  /--
  Number of involuntary context switches (process preempted)
  -/
  involuntaryContextSwitches : UInt64
deriving Repr, Inhabited


/--
A process identifier, represented by a numeric ID in UNIX systems (e.g. 1000).
-/
structure PId where
  /--
  The numeric process ID.
  -/
  toUInt64 : UInt64
deriving Inhabited, DecidableEq, Ord

instance : Repr PId where
  reprPrec u := Repr.addAppParen ("PId.mk " ++ repr u.toUInt64)

/--
Gets the title of the current process.
-/
@[inline]
def getProcessTitle : IO String :=
  UV.System.getProcessTitle

/--
Sets the title of the current process.
-/
@[inline]
def setProcessTitle (title : String) : IO Unit :=
  UV.System.setProcessTitle title

/--
Gets the current process id.
-/
@[inline]
def getId : IO PId :=
  PId.mk <$> UV.System.osGetPid

/--
Gets the current process parent id.
-/
@[inline]
def getParentId : IO PId :=
  PId.mk <$> UV.System.osGetPpid

/--
Gets the current working directory.
-/
@[inline]
def getCwd : IO System.FilePath :=
  UV.System.cwd

/--
Changes the current working directory to a new one.
-/
@[inline]
def setCwd (path : System.FilePath) : IO Unit :=
  UV.System.chdir path.toString

/--
Gets the scheduling priority of a process.
-/
@[inline]
def getPriority (pid : PId) : IO Int64 :=
  UV.System.osGetPriority pid.toUInt64

/--
Sets the scheduling priority of a process.
-/
@[inline]
def setPriority (pid : PId) (priority : Int64) : IO Unit :=
  UV.System.osSetPriority pid.toUInt64 priority

/--
Retrieves resource usage statistics.
-/
@[inline]
def getResourceUsage : IO ResourceUsageStats :=
  UV.System.getrusage <&> fun rusage =>
    {
      cpuUserTime := .ofNat <| UInt64.toNat rusage.userTime
      cpuSystemTime := .ofNat <| UInt64.toNat rusage.systemTime
      peakResidentSetSizeKb := rusage.maxRSS
      sharedMemorySizeKb := rusage.ixRSS
      unsharedDataSizeKb := rusage.idRSS
      unsharedStackSizeKb := rusage.isRSS
      minorPageFaults := rusage.minFlt
      majorPageFaults := rusage.majFlt
      swapOperations := rusage.nSwap
      blockInputOps := rusage.inBlock
      blockOutputOps := rusage.outBlock
      messagesSent := rusage.msgSent
      messagesReceived := rusage.msgRecv
      signalsReceived := rusage.signals
      voluntaryContextSwitches := rusage.voluntaryCS
      involuntaryContextSwitches := rusage.involuntaryCS
    }

/--
Returns the absolute path of the current executable.
-/
@[inline]
def getExecutablePath : IO FilePath :=
  FilePath.mk <$> UV.System.exePath

/--
Returns the amount of free system memory in bytes.
-/
@[inline]
def freeMemory : IO UInt64 :=
  UV.System.freeMemory

/--
Returns the total system memory in bytes.
-/
@[inline]
def totalMemory : IO UInt64 :=
  UV.System.totalMemory

/--
Returns the constrained memory limit in bytes.
-/
@[inline]
def constrainedMemory : IO UInt64 :=
  UV.System.constrainedMemory

/--
Returns the available memory for allocation in bytes.
-/
@[inline]
def availableMemory : IO UInt64 :=
  UV.System.availableMemory

end Process
end IO
end Internal
end Std

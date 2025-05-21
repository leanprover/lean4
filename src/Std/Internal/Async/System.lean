/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time
import Std.Internal.UV.System
import Std.Data.HashMap

/-!
This module contains all system related functions and environment variables
manipulation.
-/

open Std Time

namespace Std
namespace Internal
namespace IO
namespace Async
namespace System

/--
Represents the breakdown of CPU time usage in milliseconds.
-/
structure CPUTimes where

  /--
  Time spent in user mode.
  -/
  userTime : Millisecond.Offset

  /--
  Time spent on low-priority user processes.
  -/
  niceTime : Millisecond.Offset

  /--
  time spent in kernel mode.
  -/
  systemTime : Millisecond.Offset

  /--
  Time the CPU was idle.
  -/
  idleTime : Millisecond.Offset

  /--
  Time spent servicing hardware interrupts.
  -/
  interruptTime  : Millisecond.Offset
deriving Inhabited, DecidableEq, Repr

/--
Information about a single CPU core.
-/
structure CPUInfo where
  /--
  CPU model name.
  -/
  model : String

  /--
  The approximate clock speed of the CPU core in MHz.
  -/
  speed : Nat

  /--
  The time spent on the CPU.
  -/
  times : CPUTimes
deriving Inhabited, DecidableEq, Repr

/--
Gets information about the operating system.
-/
structure OSInfo where
  /--
  OS name.
  -/
  name : String

  /--
  OS version.
  -/
  release : String

  /--
  OS build.
  -/
  version : String

  /--
  CPU architecture.
  -/
  machine : String
deriving Repr, Inhabited

/--
All the environment variables.
-/
structure Environment where
  private mk ::
  /--
  The list of all environment variables.
  -/
  private toHashMap : HashMap String String
deriving Inhabited, Repr

@[inline]
def Environment.get (env : Environment) (key : String) : Option String :=
  env.toHashMap[key]?

/--
Gets information about the operating system.
-/
def getSystemInfo : IO OSInfo := do
  let uname ← UV.System.osUname
  return {
    name := uname.sysname
    release := uname.release
    version := uname.version
    machine := uname.machine
  }

/--
Gets information about the CPU cores.
-/
def getCPUInfo : IO (Array CPUInfo) := do
  let cpuinfo ← UV.System.cpuInfo
  return cpuinfo.map fun coreInfo =>
    {
      model := coreInfo.model
      speed := UInt64.toNat <| coreInfo.speed
      times := {
        userTime := Millisecond.Offset.ofNat <| UInt64.toNat <| coreInfo.times.user
        niceTime := Millisecond.Offset.ofNat <| UInt64.toNat <| coreInfo.times.nice
        systemTime := Millisecond.Offset.ofNat <| UInt64.toNat <| coreInfo.times.sys
        idleTime := Millisecond.Offset.ofNat <| UInt64.toNat <| coreInfo.times.idle
        interruptTime := Millisecond.Offset.ofNat <| UInt64.toNat <| coreInfo.times.irq
      }
    }

/--
Gets the system uptime in seconds.
-/
@[inline]
def getUpTime : IO Second.Offset := do
  return .ofNat <| UInt64.toNat (← UV.System.uptime)

/--
Gets the system uptime in seconds.
-/
@[inline]
def getHighResolutionTime : IO Nanosecond.Offset := do
  return .ofNat <| UInt64.toNat <| (← UV.System.hrtime)

/--
Gets the hostname of the machine.
-/
@[inline]
def getHostName : IO String :=
  UV.System.osGetHostname

/--
Sets an environment variable to `value`.
-/
@[inline]
def setEnvVar (name : String) (value : String) : IO Unit := do
  UV.System.osSetenv name value

/--
Gets an environment variable.
-/
@[inline]
def getEnvVar (name : String) : IO (Option String) :=
  UV.System.osGetenv name

/--
Unset an environment variable.
-/
@[inline]
def unsetEnvVar (name : String) : IO Unit := do
  UV.System.osUnsetenv name

/--
Gets all environment variables.
-/
@[inline]
def getEnv : IO Environment := do
  let array ← UV.System.osEnviron
  return ⟨HashMap.ofList array.toList⟩

/--
Gets the current user's home directory.
-/
@[inline]
def getHomeDir : IO String :=
  UV.System.osHomedir

/--
Gets the temporary directory.
-/
@[inline]
def getTmpDir : IO String := do
  UV.System.osTmpdir

end System
end Async
end IO
end Internal
end Std

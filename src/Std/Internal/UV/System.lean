/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Sofia Rodrigues
-/
module

prelude
public import Init.System.Promise
public import Init.Data.SInt
public import Std.Net

@[expose] public section

namespace Std
namespace Internal
namespace UV
namespace System

open Std.Net

/--
Represents resource usage statistics for a process or thread.
All time values are in milliseconds.
-/
structure RUsage where
  userTime : UInt64
  systemTime : UInt64
  maxRSS : UInt64
  ixRSS : UInt64
  idRSS : UInt64
  isRSS : UInt64
  minFlt : UInt64
  majFlt : UInt64
  nSwap : UInt64
  inBlock : UInt64
  outBlock : UInt64
  msgSent : UInt64
  msgRecv : UInt64
  signals : UInt64
  voluntaryCS : UInt64
  involuntaryCS : UInt64
deriving Repr, Inhabited

/--
Represents the breakdown of CPU time usage in milliseconds.
-/
structure CPUTimes where
  user : UInt64
  nice : UInt64
  sys : UInt64
  idle : UInt64
  irq : UInt64
deriving Repr, Inhabited

/--
Information about a single CPU core.
-/
structure CPUInfo where
  model : String
  speed : UInt64
  times : CPUTimes
deriving Repr, Inhabited

/--
Information about the current user.
-/
structure PasswdInfo where
  username : String
  uid : Option UInt64
  gid : Option UInt64
  shell : Option String
  homedir : Option String
deriving Repr, Inhabited

/--
Information about the current group,
-/
structure GroupInfo where
  groupname : String
  gid : UInt64
  members : Array String
deriving Repr, Inhabited

/--
Information about the OS.
-/
structure UnameInfo where
  sysname : String
  release : String
  version : String
  machine : String
deriving Repr, Inhabited

/--
Gets the title of the current process.
-/
@[extern "lean_uv_get_process_title"]
opaque getProcessTitle : IO String

/--
Sets the title of the current process.
-/
@[extern "lean_uv_set_process_title"]
opaque setProcessTitle : @& String → IO Unit

/--
Gets the system uptime in seconds.
-/
@[extern "lean_uv_uptime"]
opaque uptime : IO UInt64

/--
Gets the process ID of the current process.
-/
@[extern "lean_uv_os_getpid"]
opaque osGetPid : IO UInt64

/--
Gets the parent process ID of the current process.
-/
@[extern "lean_uv_os_getppid"]
opaque osGetPpid : IO UInt64

/--
Gets information about the system's CPUs.
-/
@[extern "lean_uv_cpu_info"]
opaque cpuInfo : IO (Array CPUInfo)

/--
Gets the current working directory.
-/
@[extern "lean_uv_cwd"]
opaque cwd : IO String

/--
Changes the current working directory.
-/
@[extern "lean_uv_chdir"]
opaque chdir : @& String → IO Unit

/--
Gets the path to the current user's home directory.
-/
@[extern "lean_uv_os_homedir"]
opaque osHomedir : IO String

/--
Gets the path to the temporary directory.
-/
@[extern "lean_uv_os_tmpdir"]
opaque osTmpdir : IO String

/--
Gets a subset of the password file entry for the current user.
-/
@[extern "lean_uv_os_get_passwd"]
opaque osGetPasswd : IO PasswdInfo

/--
Gets information about the current user's group.
-/
@[extern "lean_uv_os_get_group"]
opaque osGetGroup : UInt64 → IO (Option GroupInfo)

/--
Gets all environment variables.
-/
@[extern "lean_uv_os_environ"]
opaque osEnviron : IO (Array (String × String))

/--
Gets the value of an environment variable.
-/
@[extern "lean_uv_os_getenv"]
opaque osGetenv : String → IO (Option String)

/--
Sets the value of an environment variable.
-/
@[extern "lean_uv_os_setenv"]
opaque osSetenv : String → String → IO Unit

/--
Unsets an environment variable.
-/
@[extern "lean_uv_os_unsetenv"]
opaque osUnsetenv : String → IO Unit

/--
Gets the hostname of the machine.
-/
@[extern "lean_uv_os_gethostname"]
opaque osGetHostname : IO String

/--
Gets the scheduling priority of a process.
-/
@[extern "lean_uv_os_getpriority"]
opaque osGetPriority : UInt64 → IO Int64

/--
Sets the scheduling priority of a process.
-/
@[extern "lean_uv_os_setpriority"]
opaque osSetPriority : UInt64 → Int64 → IO Unit

/--
Gets information about the operating system.
-/
@[extern "lean_uv_os_uname"]
opaque osUname : IO UnameInfo

/--
Gets the current high-resolution time in nanoseconds.
-/
@[extern "lean_uv_hrtime"]
opaque hrtime : IO UInt64

/--
Generates cryptographically secure random bytes.
-/
@[extern "lean_uv_random"]
opaque random : UInt64 → IO (IO.Promise (Except IO.Error ByteArray))

/--
Retrieves resource usage statistics.
-/
@[extern "lean_uv_getrusage"]
opaque getrusage : IO RUsage

/--
Returns the absolute path of the current executable.
-/
@[extern "lean_uv_exepath"]
opaque exePath : IO String

/--
Returns the amount of free system memory in bytes.
-/
@[extern "lean_uv_get_free_memory"]
opaque freeMemory : IO UInt64

/--
Returns the total system memory in bytes.
-/
@[extern "lean_uv_get_total_memory"]
opaque totalMemory : IO UInt64

/--
Returns the constrained memory limit in bytes.
-/
@[extern "lean_uv_get_constrained_memory"]
opaque constrainedMemory : IO UInt64

/--
Returns the available memory for allocation in bytes.
-/
@[extern "lean_uv_get_available_memory"]
opaque availableMemory : IO UInt64

end System
end UV
end Internal
end Std

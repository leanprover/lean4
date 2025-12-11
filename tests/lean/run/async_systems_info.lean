import Std.Internal.Async.System
import Std.Internal.Async.Process
import Lean.Runtime

open Std.Internal.IO.Async.System
open Std.Internal.IO.Process

#eval do
  assert! (← getUpTime) > 0

#eval do
  assert! (← getHighResolutionTime) > 0

#eval do
  assert! (← getHostName) != ""

#eval do
  setEnvVar "TEST_LEAN_ASYNC" "hello world"

#eval do
  assert! (← getEnvVar "TEST_LEAN_ASYNC") == (some "hello world")

#eval do
  assert! (← getEnv).get? "TEST_LEAN_ASYNC" == (some "hello world")

#eval
  unsetEnvVar "TEST_LEAN_ASYNC"

#eval do
  assert! (← getEnvVar "TEST_LEAN_ASYNC") == none

#eval do
  assert! (← getSystemInfo).machine != ""

#eval do
  assert! (← getCPUInfo).size > 0

#eval do
  assert! (← getHomeDir) != ""

#eval do
  assert! (← getTmpDir) != ""

#eval do
  assert! (← getId).toUInt64 != 0

#eval do
  assert! (← getParentId).toUInt64 != 0

#eval do
  let cwd ← getCwd
  assert! cwd.toString != ""

#eval do
  let cwd ← getCwd
  setCwd cwd

#eval do
  if System.Platform.isWindows then
    return

  let pid ← getId
  setPriority pid 3
  assert! (← getPriority pid) == 3

#eval do
  if System.Platform.isWindows then
    return

  let pid ← getParentId
  setPriority pid 3
  assert! (← getPriority pid) == 3

#eval do
  if System.Platform.isWindows then
    return

  let user ← getCurrentUser
  if System.Platform.isWindows then
    assert! user.userId == none
    assert! user.groupId == none
  else
    assert! user.userId != none
    assert! user.username != ""

#eval do
  if System.Platform.isWindows then
    return
  if Lean.libUVVersion < 0x012D00 then
    return

  assert! (← getGroup (GroupId.mk 240000)).isNone

#eval do
  assert! (← getResourceUsage).peakResidentSetSizeKb > 0

#eval do
  assert! (← getExecutablePath) != ""

#eval do
  assert! (← freeMemory) > 0

#eval do
  assert! (← totalMemory) > 0

#eval
  constrainedMemory

#eval do
  if Lean.libUVVersion < 0x012D00 then
    return

  assert! (← availableMemory) > 0

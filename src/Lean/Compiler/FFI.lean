/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Data.Array.Basic
import Init.System.FilePath

open System

namespace Lean.Compiler.FFI

@[extern "lean_get_leanc_extra_flags"]
private opaque getLeancExtraFlags : Unit → String

private def flagsStringToArray (s : String) : Array String :=
  s.splitOn.toArray |>.filter (· ≠ "")

/-- Return C compiler flags for including Lean's headers. -/
def getCFlags (leanSysroot : FilePath) : Array String :=
  #["-I", (leanSysroot / "include").toString] ++ flagsStringToArray (getLeancExtraFlags ())

@[extern "lean_get_leanc_internal_flags"]
private opaque getLeancInternalFlags : Unit → String

/-- Return C compiler flags needed to use the C compiler bundled with the Lean toolchain. -/
def getInternalCFlags (leanSysroot : FilePath) : Array String :=
  flagsStringToArray (getLeancInternalFlags ()) |>.map (·.replace "ROOT" leanSysroot.toString)

@[extern "lean_get_linker_flags"]
private opaque getBuiltinLinkerFlags (linkStatic : Bool) : String

/-- Return linker flags for linking against Lean's libraries. -/
def getLinkerFlags (leanSysroot : FilePath) (linkStatic := true) : Array String :=
  #["-L", (leanSysroot / "lib" / "lean").toString] ++ flagsStringToArray (getBuiltinLinkerFlags linkStatic)

@[extern "lean_get_internal_linker_flags"]
private opaque getBuiltinInternalLinkerFlags : Unit → String

/-- Return linker flags needed to use the linker bundled with the Lean toolchain. -/
def getInternalLinkerFlags (leanSysroot : FilePath) : Array String :=
  flagsStringToArray (getBuiltinInternalLinkerFlags ()) |>.map (·.replace "ROOT" leanSysroot.toString)

end Lean.Compiler.FFI

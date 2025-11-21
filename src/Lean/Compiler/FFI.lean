/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.System.FilePath
import Init.Data.String.Search

public section

open System

namespace Lean.Compiler.FFI

@[extern "lean_get_leanc_extra_flags"]
private opaque getLeancExtraFlags : Unit → String

private def flagsStringToArray (s : String) : Array String :=
  s.split ' ' |>.filter (!·.isEmpty) |>.toStringArray

/--
Return C compiler flags for including Lean's headers.
Unlike `getCFlags`, this does not contain the Lean include directory.
-/
def getCFlags' : Array String :=
  flagsStringToArray (getLeancExtraFlags ())

/-- Return C compiler flags for including Lean's headers. -/
def getCFlags (leanSysroot : FilePath) : Array String :=
  #["-I", (leanSysroot / "include").toString] ++ getCFlags'

@[extern "lean_get_leanc_internal_flags"]
private opaque getLeancInternalFlags : Unit → String

/-- Return C compiler flags needed to use the C compiler bundled with the Lean toolchain. -/
def getInternalCFlags (leanSysroot : FilePath) : Array String :=
  flagsStringToArray (getLeancInternalFlags ()) |>.map (·.replace "ROOT" leanSysroot.toString)

@[extern "lean_get_linker_flags"]
private opaque getBuiltinLinkerFlags (linkStatic : Bool) : String

/--
Return linker flags for linking against Lean's libraries.
Unlike `getLinkerFlags`, this does not contain the Lean library directory.
-/
def getLinkerFlags' (linkStatic := true) : Array String :=
  flagsStringToArray (getBuiltinLinkerFlags linkStatic)

/-- Return linker flags for linking against Lean's libraries. -/
def getLinkerFlags (leanSysroot : FilePath) (linkStatic := true) : Array String :=
  #["-L", (leanSysroot / "lib" / "lean").toString] ++ getLinkerFlags' linkStatic

@[extern "lean_get_internal_linker_flags"]
private opaque getBuiltinInternalLinkerFlags : Unit → String

/-- Return linker flags needed to use the linker bundled with the Lean toolchain. -/
def getInternalLinkerFlags (leanSysroot : FilePath) : Array String :=
  flagsStringToArray (getBuiltinInternalLinkerFlags ()) |>.map (·.replace "ROOT" leanSysroot.toString)

end Lean.Compiler.FFI

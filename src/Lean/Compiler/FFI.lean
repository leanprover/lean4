/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

open System

namespace Lean.Compiler.FFI

@[extern "lean_get_leanc_extra_flags"]
private opaque getLeancExtraFlags : Unit → String

/-- Return C compiler flags for including Lean's headers. -/
def getCFlags (leanSysroot : FilePath) : Array String :=
  #["-I", (leanSysroot / "include").toString] ++ (getLeancExtraFlags ()).trim.splitOn

@[extern "lean_get_linker_flags"]
private opaque getBuiltinLinkerFlags (linkStatic : Bool) : String

/-- Return linker flags for linking against Lean's libraries. -/
def getLinkerFlags (leanSysroot : FilePath) (linkStatic := true) : Array String :=
  #["-L", (leanSysroot / "lib" / "lean").toString] ++ (getBuiltinLinkerFlags linkStatic).trim.splitOn

end Lean.Compiler.FFI

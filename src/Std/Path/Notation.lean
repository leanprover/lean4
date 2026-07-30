/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Path.Basic
public meta import Std.Path.Basic
public meta import Init.Data.String.Defs

public section

/-!
# Path literals

`path("src/Main.lean")` parses a POSIX-style path literal at elaboration time, so an invalid
literal (empty, or containing a null byte) is a compile-time error instead of a runtime panic.
-/

namespace Std

/--
Parses a POSIX-style path literal at elaboration time using `Path.ofPosixString`. An invalid
literal (empty, or containing a null byte) is a compile-time error instead of a runtime panic.

Example:
`path("src/Main.lean")`
-/
syntax "path(" str ")" : term

macro_rules
  | `(path($s)) =>
    match Path.ofPosixString s.getString with
    | some _ => `(Path.ofPosixString! $s)
    | none => Lean.Macro.throwErrorAt s s!"invalid path: {s.getString.quote}"

end Std

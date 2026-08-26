/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Path.Basic
public import Std.Path.Notation

public section

/-!
# Path

A platform-neutral file system path library for Lean.

A `Path` is a parsed path: an `Array Path.Component`, where a component is a Windows prefix, a root
separator, `.`, `..`, or a normal segment.

- All structural operations (`join`, `parent`, `normalize`, `startsWith`, …) are **pure**: they work
  on the component array without OS calls or string scanning.

- Platform-specific behaviour is confined to `IO` actions: `Path.fromString` and `Path.toString` use
  the runtime separator; `Path.resolve` calls into the OS.

`Std.Path` is meant to replace `System.FilePath`, which stores a path as a plain `String` and
rescans it for separators on every operation.

## Quick Start

```lean
import Std.Path

open Std

-- Pure construction from known-format strings (`ofPosixString` returns `Option Path`)
def p : Path := Path.ofPosixString "/usr/local/bin/lean" |>.get!

#eval p.fileName             -- some { value := "lean", proof := ... }
#eval p.extension            -- none
#eval p.parent.map (·.toPosixString)  -- some "/usr/local/bin"

-- Join with /
def q := p / (Path.ofPosixString "lib" |>.get!)
#eval q.toPosixString        -- "/usr/local/bin/lean/lib"

-- Platform-sensitive parsing (IO)
def main : IO Unit := do
  let home ← Path.fromString ((← IO.getEnv "HOME").getD "")
  let cfg := home / (Path.ofPosixString ".config/lean" |>.get!)
  IO.println (← cfg.toString)
```

## Path literals

`path("src/Main.lean")` parses a POSIX-style path literal at elaboration time, failing with a
compile-time error (instead of a runtime panic) on invalid input:

```lean
#eval (path("src/Main.lean")).toPosixString  -- "src/Main.lean"
```

## Glob matching

`Path.matchGlob` tests a path against a `/`-separated glob pattern, supporting `*`, `?`,
`[abc]`/`[a-z]`/`[!abc]` character classes, and `**` for zero or more whole segments:

```lean
#eval (Path.ofPosixString "src/Std/Path.lean" |>.get!).matchGlob "src/**/*.lean"  -- true
```
-/

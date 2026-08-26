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

A `Path` is a parsed path: a `Path.Anchor` — what the path is anchored to — plus an
`Array Path.Segment` of `.`, `..`, and ordinary names below it.

- The **anchor** carries every platform-specific decision: `.neutral` for a plain relative path like
  `src/Main.lean`, `.posix` for `/usr`, and `.windows` for `C:\Users`, `C:foo`, `\foo`, or
  `\\server\share`. Whether a path is POSIX or Windows, absolute or relative, is read off the anchor
  alone rather than inferred from what its text happens to look like.

- The **segments** mean the same thing on both platforms, so an unanchored (`.neutral`) path renders
  correctly in either syntax and joins onto an anchor of either flavour. Parsing `a/b` as POSIX and
  `a\b` as Windows produces the same value.

- All structural operations (`join`, `parent`, `normalize`, `startsWith`, …) are **pure**: they work
  on the anchor and segment array without OS calls or string scanning.

- Platform-specific behaviour is confined to `IO` actions: `Path.fromBytes` and `Path.toBytes` use
  the runtime separator; `Path.resolve` calls into the OS.

`Std.Path` is meant to replace `System.FilePath`, which stores a path as a plain `String` and
rescans it for separators on every operation.

## Bytes, not strings

Segments and prefixes store raw bytes. A path is an arbitrary byte string on POSIX and a possibly
ill-formed UTF-16 string on Windows, so on neither platform is it guaranteed to be valid UTF-8, and
a `String` cannot hold every path the OS can hand back.

That splits the API in two. `ofPosixBytes`/`toPosixBytes` (and their Windows and platform-native
counterparts, `fromBytes`/`toBytes`) parse and render paths **losslessly**. The `String` versions —
`ofPosixString`, `toPosixString`, `fromString`, `toString`, `Filename.toString`, … — are
conveniences on top: encoding a `String` loses nothing, but decoding back replaces every byte that
is not part of a well-formed UTF-8 encoding with `U+FFFD`. Reach for the byte functions whenever a
path may not have come from a `String` — everything the OS hands back, including `cwd` and
`resolve`, goes through them.

## Quick Start

```lean
import Std.Path

open Std

-- Pure construction from known-format strings (`ofPosixString` returns `Option Path`)
def p : Path := Path.ofPosixString "/usr/local/bin/lean" |>.get!

#eval p.fileName.map toString   -- some "lean"
#eval p.extension.isSome        -- false
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

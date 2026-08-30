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

A `Path` is a parsed path: a `Path.Anchor` what the path is anchored to plus an
`Array Path.Segment` of `.`, `..`, and ordinary names below it.

- The **anchor** carries every platform-specific decision: `.neutral` for a plain relative path like
  `src/Main.lean`, `.posix` for `/usr`, and `.windows` for `C:\Users`, `C:foo`, `\foo`, or
  `\\server\share`. Whether a path is POSIX or Windows, absolute or relative, is read off the anchor
  alone rather than inferred from what its text happens to look like.

- The **segments** mean the same thing on both platforms, so an unanchored (`.neutral`) path renders
  correctly in either syntax and joins onto an anchor of either flavour. Parsing `a/b` as POSIX and
  `a\b` as Windows produces the same value.

- All structural operations (`join`, `parent?`, `normalize`, `startsWith`, …) are **pure**: they work
  on the anchor and segment array without OS calls or string scanning.

- Platform-specific behaviour is confined to `IO` actions: `Path.ofBytes` and `Path.toBytes` use
  the runtime separator; `Path.resolve` calls into the OS.

- A `.` **is not a component**. It is kept in `segments`, so rendering stays lossless, but every
  operation that asks what a path names — `Path.components` and, through it, `==`, `compare`,
  `hash`, `parent?`, `filename?`, `startsWith`, `endsWith`, `matchGlob`, … — reads straight past it,
  so `a/./b` and `a/b` are one path. A `..` is a component and is never resolved without asking the
  file system, since a symbolic link makes `a/..` and `.` different directories.

- Paths **compare, sort, and print**. `==`, `compare`, and `hash` agree with one another and all
  three fold the case of a Windows drive letter, so `c:\foo` and `C:\foo` are the same path to each
  of them while `=` still separates them. `#eval` shows a path as the call that rebuilds it —
  `Std.Path.ofPosixString! "/usr/bin"` — falling back to the anchor and segments spelled out for the
  paths no such call reproduces.

`Std.Path` is meant to replace `System.FilePath`, which stores a path as a plain `String` and
rescans it for separators on every operation.

## Bytes, not strings

Segments and prefixes store raw bytes. A path is an arbitrary byte string on POSIX and a possibly
ill-formed UTF-16 string on Windows, so on neither platform is it guaranteed to be valid UTF-8, and
a `String` cannot hold every path the OS can hand back.

That splits the API in two. `ofPosixBytes?`/`toPosixBytes` (and their Windows and platform-native
counterparts, `ofBytes`/`toBytes`) parse and render paths **losslessly**. Rendering across
flavours is lossy in a second way — a Windows prefix has no POSIX spelling, and a POSIX name can
hold Windows syntax — and lossy silently, since the result is another well-formed path:
`\\server\share` renders as `.` under POSIX syntax. `toPosixBytes?`/`toWindowsBytes?` rule that
out by reading the render back, which is the check `toBytes` applies for the host; use them
wherever the result goes on to name a file. The `String` versions —
`ofPosixString?`, `toPosixString`, `ofString`, `toString`, `Filename.toString`, … — are
conveniences on top: encoding a `String` loses nothing, but decoding back replaces every byte that
is not part of a well-formed UTF-8 encoding with `U+FFFD`. Reach for the byte functions whenever a
path may not have come from a `String` — everything the OS hands back, including `cwd` and
`resolve`, goes through them.

## Quick Start

```lean
import Std.Path

open Std

-- Pure construction from known-format strings (`ofPosixString?` returns `Option Path`)
def p : Path := Path.ofPosixString! "/usr/local/bin/lean"

#eval p.filename?.map toString   -- some "lean"
#eval p.extension?.isSome        -- false
#eval p.parent?.map (·.toPosixString)  -- some "/usr/local/bin"

-- Join with /
def q := p / (Path.ofPosixString! "lib")
#eval q.toPosixString        -- "/usr/local/bin/lean/lib"

-- Platform-sensitive parsing (IO)
def main : IO Unit := do
  let cfg := (← Path.homeDir) / (Path.ofPosixString! ".config/lean")
  IO.println (← cfg.toString)
```

## Locations the OS names

`Path.currentDir`, `Path.homeDir`, and `Path.tempDir` read the working, home, and temporary
directories as raw bytes, so a directory whose name is not valid UTF-8 survives intact.
`Path.exeExtension` gives the extension an executable binary carries on the host, and
`Path.SearchPath` splits and rejoins a `PATH`-style list on the host's separator.

## Path literals

`path("src/Main.lean")` parses a POSIX-style path literal at elaboration time, failing with a
compile-time error (instead of a runtime panic) on invalid input:

```lean
#eval (path("src/Main.lean")).toPosixString  -- "src/Main.lean"
```

## Glob matching

`Path.matchGlob` tests a path against a `/`-separated glob pattern, supporting `*`, `?`,
`[abc]`/`[a-z]`/`[!abc]` character classes, and `**` for whole segments — zero or more of them
before a further segment, one or more at the end of the pattern:

```lean
#eval (Path.ofPosixString! "src/Std/Path.lean").matchGlob "src/**/*.lean"  -- true
```

Matching is case-sensitive; pass `caseInsensitive := true` to fold ASCII letters instead.

## Taking a path from somewhere else

A path that arrived from outside the program — a request, an archive entry, a configuration file —
is input, and the operations below are the ones that treat it as such.

`Path.resolveWithin` is the only one that gives an answer about the file system. It resolves a
relative path beneath a base directory and fails unless it really lands there, so a symbolic link
pointing out of the tree is caught even when a `..` behind it makes the path look contained. The
answer is about the moment of the call and not about the moment the caller uses it: nothing stops
another process from replacing a component with a symbolic link in between, so open the result and
work from the handle rather than re-deriving the path.

Everything else is lexical, and lexical answers are about spelling:

- `Path.joinRelative?` refuses a right-hand side that is anchored, which under `join` would replace
  the base rather than extend it — `"/srv/uploads"` joined with `"/etc/passwd"` is `/etc/passwd`.
- `Path.isUnder` resolves `.` and `..` in both paths and asks whether one is below the other. It is
  sound only where no segment above a `..` is a symbolic link, so use it to reject obviously
  escaping input rather than to admit input as safe.
- `Path.isNormalized` says whether a path is already free of `.` and of `..` that something cancels.
- `Path.startsWith`, `Path.endsWith`, and `Path.matchGlob` compare a path as written, leaving `..`
  unresolved. `"uploads/../secret"` matches `"uploads/**"`.

Two things these comparisons do not know about:

- **Case.** Names are compared byte for byte, so `"/etc"` and `"/ETC"` are different paths to `==`,
  `compare`, `isUnder`, and `startsWith`, while Windows and macOS default to file systems that treat
  them as one name. Whether case matters is a property of the file system a path lands on rather
  than of the platform it was written for — Linux has case-folding directories and Windows has
  case-sensitive ones — so it is not something the type can settle. Where a comparison has to hold
  against the file system, resolve first.
- **Windows short names.** `PROGRA~1` and `Program Files` name one directory, and only the file
  system knows which pairs those are.

`Path.isWindowsPortable` covers the other direction: names that mean something else to Windows than
they say. Win32 strips a trailing `.` or space from a name, reserves `CON`, `NUL`, `COM1` and their
relatives in every directory, and keeps `"`, `*`, `:`, `<`, `>`, `?` and `|` for itself, so
`dir/foo.` reaches `dir\foo` and `a/b:c` opens an alternate data stream. Each of those is an
ordinary POSIX file name that `Filename` accepts, which is why the check lives at the Windows
boundary: `toWindowsBytes?` and, on a Windows host, `toBytes` refuse a path it rejects.
-/

import Std.Path.Notation

/-!
Tests for the `path(...)` literal macro (`Std.Path.Notation`) — parses a POSIX-style path string
at elaboration time, failing at compile time (rather than panicking at runtime) on invalid input.
-/

open Std

-- absolute / relative literals round-trip through `toPosixString`
#guard (path("src/Main.lean")).toPosixString = "src/Main.lean"
#guard (path("/usr/local/bin")).toPosixString = "/usr/local/bin"

-- agrees with the equivalent `ofPosixString!` construction
#guard path("a") == Path.ofPosixString! "a"

-- usable with the rest of the pure API, e.g. `/`
#guard path("a") / path("b") == path("a/b")

-- `.`, `..`, non-ASCII names and repeated separators all survive the parse
#guard path("a/./../b").segments.map toString = #["a", ".", "..", "b"]
#guard path("a//b/").toPosixString = "a/b"
#guard path("héllo/wörld").toPosixString = "héllo/wörld"

-- invalid literal (empty string) is a compile-time error, not a runtime panic
/-- error: invalid path: "" -/
#guard_msgs in
#eval path("")

-- invalid literal (null byte) is a compile-time error, not a runtime panic
/-- error: invalid path: "a\x00b" -/
#guard_msgs in
#eval path("a\x00b")

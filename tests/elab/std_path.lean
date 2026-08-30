import Std.Path
import Std.Data.HashMap

/-!
Tests for `Std.Path` — covers parsing, rendering, structural operations, file-name helpers,
normalization, glob matching, and the `parents` iterator.
-/

open Std

-- Helpers to cut noise
private def posix (s : String) : Path := (Path.ofPosixString? s).get!
private def win   (s : String) : Path := (Path.ofWindowsString? s).get!


-- ---------------------------------------------------------------------------
-- Section: ofPosixString? / toPosixString round-trips
-- ---------------------------------------------------------------------------

section PosixRoundtrip

-- absolute
#guard (posix "/usr/local/bin").toPosixString = "/usr/local/bin"
-- relative
#guard (posix "a/b/c").toPosixString = "a/b/c"
-- root only
#guard (posix "/").toPosixString = "/"
-- single segment
#guard (posix "foo").toPosixString = "foo"
-- current dir
#guard (posix "./foo").toPosixString = "./foo"
-- parent dir
#guard (posix "../bar").toPosixString = "../bar"
-- multiple leading slashes collapsed to one root
#guard (posix "///a/b").toPosixString = "/a/b"
-- trailing slash not preserved (no trailing empty segment)
#guard (posix "a/b/").toPosixString = "a/b"
-- dot segment preserved
#guard (posix "a/./b").toPosixString = "a/./b"
-- double-dot preserved
#guard (posix "a/../b").toPosixString = "a/../b"
-- empty string → none
#guard Path.ofPosixString? "" = none
-- null byte → none (invalid on every platform)
#guard Path.ofPosixString? "a\x00b" = none
-- ofPosixString! agrees with ofPosixString? on valid input
#guard Path.ofPosixString! "/usr/local/bin" == posix "/usr/local/bin"

end PosixRoundtrip


-- ---------------------------------------------------------------------------
-- Section: ofWindowsString? / toWindowsString round-trips
-- ---------------------------------------------------------------------------

section WindowsRoundtrip

-- absolute drive path
#guard (win "C:\\Users\\foo").toWindowsString = "C:\\Users\\foo"
-- drive + forward slashes
#guard (win "C:/Users/foo").toWindowsString = "C:\\Users\\foo"
-- root-only drive
#guard (win "C:\\").toWindowsString = "C:\\"
-- relative, no drive
#guard (win "a\\b\\c").toWindowsString = "a\\b\\c"
-- mixed separators normalised to backslash
#guard (win "C:\\a/b\\c").toWindowsString = "C:\\a\\b\\c"
-- dot and parent preserved
#guard (win "C:\\a\\.\\..\\b").toWindowsString = "C:\\a\\.\\..\\b"
-- POSIX path through Windows parser: only '/' is also a separator
#guard (win "/foo/bar").toWindowsString = "\\foo\\bar"
-- toPosixString on a Windows path silently drops the drive prefix
#guard (win "C:\\foo").toPosixString = "/foo"
-- trailing separator not preserved (parity with the POSIX parser)
#guard (win "C:\\Users\\foo\\").toWindowsString = "C:\\Users\\foo"
#guard (win "a\\b\\").toWindowsString = "a\\b"
-- repeated separators collapsed (no silent truncation of later segments)
#guard (win "C:\\\\Users\\\\foo").toWindowsString = "C:\\Users\\foo"
#guard (win "a//b").toWindowsString = "a\\b"
-- root-only with trailing slashes
#guard (win "\\\\").toWindowsString = "\\"
-- empty string → none (parity with ofPosixString?)
#guard Path.ofWindowsString? "" = none
-- null byte → none (parity with ofPosixString?)
#guard Path.ofWindowsString? "a\x00b" = none
-- ofWindowsString! agrees with ofWindowsString? on valid input
#guard Path.ofWindowsString! "C:\\Users\\foo" == win "C:\\Users\\foo"
-- a leading "\\" introduces a prefix rather than collapsing to a root (see the Prefix section)
#guard (win "\\\\server\\share").toWindowsString = "\\\\server\\share"

end WindowsRoundtrip


-- ---------------------------------------------------------------------------
-- Section: Windows prefixes (UNC, device, verbatim)
-- ---------------------------------------------------------------------------

section Prefix

-- UNC: `\\server\share` parses as one prefix, not as a root plus two segments.
#guard (win "\\\\server\\share").windowsPrefix? == some "\\\\server\\share".toByteArray
#guard (win "\\\\server\\share\\dir\\file.txt").windowsPrefix? == some "\\\\server\\share".toByteArray
#guard (win "\\\\server\\share\\dir\\file.txt").toWindowsString = "\\\\server\\share\\dir\\file.txt"
-- a server with no share
#guard (win "\\\\server").windowsPrefix? == some "\\\\server".toByteArray
#guard (win "\\\\server").toWindowsString = "\\\\server"
-- forward slashes introduce a prefix too, as on Windows itself
#guard (win "//server/share/x").toWindowsString = "\\\\server\\share\\x"
-- a bare `\\` is a root, keeping `\\` and `\` equivalent
#guard (win "\\\\").windowsPrefix? == none
#guard (win "\\\\").toWindowsString = "\\"

-- Device namespace: `\\.\name` is captured like a UNC share, so only the first segment after
-- `\\.\` belongs to the prefix.
#guard (win "\\\\.\\COM42").windowsPrefix? == some "\\\\.\\COM42".toByteArray
#guard (win "\\\\.\\COM42").toWindowsString = "\\\\.\\COM42"
#guard (win "\\\\.\\pipe\\name").windowsPrefix? == some "\\\\.\\pipe".toByteArray
#guard (win "\\\\.\\pipe\\name").toWindowsString = "\\\\.\\pipe\\name"

-- Verbatim: the prefix is `\\?\` plus the volume segment behind it; the rest splits as usual.
#guard (win "\\\\?\\C:\\foo").windowsPrefix? == some "\\\\?\\C:".toByteArray
#guard (win "\\\\?\\C:\\foo").segments.map toString = #["foo"]
#guard (win "\\\\?\\C:\\foo").toWindowsString = "\\\\?\\C:\\foo"
#guard (win "\\\\?\\cat_pics").windowsPrefix? == some "\\\\?\\cat_pics".toByteArray
#guard (win "\\\\?\\cat_pics").toWindowsString = "\\\\?\\cat_pics"
#guard (win "\\\\?\\UNC\\server\\share").windowsPrefix? == some "\\\\?\\UNC\\server\\share".toByteArray
#guard (win "\\\\?\\UNC\\server\\share").toWindowsString = "\\\\?\\UNC\\server\\share"
-- Segments below a verbatim prefix behave like any other, so file names and parents work.
#guard (win "\\\\?\\C:\\dir\\doc.txt").filename?.map toString = some "doc.txt"
#guard (win "\\\\?\\C:\\dir\\doc.txt").extension?.map toString = some "txt"
#guard (win "\\\\?\\C:\\dir\\doc.txt").parent?.map Path.toWindowsString = some "\\\\?\\C:\\dir"
-- Windows gives `/` no meaning inside a verbatim path, so it stays part of the volume name.
#guard (win "\\\\?\\a/b").windowsPrefix? == some "\\\\?\\a/b".toByteArray
#guard (win "\\\\?\\a/b").segments.isEmpty
#guard (win "\\\\?\\a\\b/c\\d").segments.map toString = #["b/c", "d"]
-- A name holding `/` is still an ordinary name, so it keeps its extension, but no `Filename` can
-- carry it and every accessor that returns one says so.
#guard (win "\\\\?\\a\\b/c.txt").fileStem? = none
#guard (win "\\\\?\\a\\b/c.txt").filePrefix? = none
#guard (win "\\\\?\\a\\b/c.txt").extension? = some (Path.Extension.mk "txt".toByteArray)
#guard (win "\\\\?\\a\\b/c.txt").suffixes = #[Path.Extension.mk "txt".toByteArray]
#guard (win "\\\\?\\a\\b/c.txt").removeExtension.toWindowsString = "\\\\?\\a\\b/c"
#guard (win "\\\\?\\a\\.hidden/x").isHidden = true
#guard (win "\\\\?\\a\\b/c.txt").filename? = none
-- `.` and `..` are ordinary names below a verbatim prefix, so they are file names there too, and
-- the usual trailing-dot rule applies: `..` is the stem `.` with an empty, and so absent, extension.
-- truncating `..` leaves `.`, which no `Filename` can carry
#guard (win "\\\\?\\a\\..").fileStem? = none
#guard (win "\\\\?\\a\\..").extension? = none
-- Windows hands a verbatim path to the filesystem unnormalized, so `.` and `..` are ordinary names
-- there and `normalize` leaves them alone.
#guard (win "\\\\?\\a\\b\\..\\c").windowsPrefix? == some "\\\\?\\a".toByteArray
#guard (win "\\\\?\\a\\b\\..\\c").segments.map toString = #["b", "..", "c"]
#guard (win "\\\\?\\a\\b\\..\\c").normalize == win "\\\\?\\a\\b\\..\\c"
#guard (win "\\\\?\\a\\.\\b").normalize.toWindowsString = "\\\\?\\a\\.\\b"
-- `normalize` leaves a verbatim path alone, so `join` is what resolves a `.` or `..` arriving from
-- a path parsed under ordinary rules — after the join there is nothing left to resolve.
#guard (win "\\\\?\\a").isVerbatim = true

-- `..a` minus its extension would be `.`, which names a directory rather than a file and would
-- re-parse as a different path, so the name is kept whole.
#guard (posix "..a").removeExtension == posix "..a"
#guard (posix "...").removeExtension == posix "..."
#guard (posix "x/..a").removeExtension == posix "x/..a"
#guard (posix "archive.tar.gz").removeExtension == posix "archive.tar"

-- No path renders as the empty byte string, which no parser would read back.
#guard Path.empty.toPosixBytes == ".".toByteArray
#guard Path.empty.toWindowsBytes == ".".toByteArray
#guard (win "\\\\?\\a/b").toPosixBytes == ".".toByteArray

-- `isUnder` resolves `.` and `..` before comparing, where `startsWith` compares as written.
#guard (posix "/safe/../etc/passwd").startsWith (posix "/safe") = true
#guard (posix "/safe/../etc/passwd").isUnder (posix "/safe") = false
#guard (posix "/safe/a/b").isUnder (posix "/safe") = true
#guard (posix "/safe").isUnder (posix "/safe") = true
#guard (posix "/safebar").isUnder (posix "/safe") = false
#guard (posix "a/../../b").isUnder (posix "a") = false
#guard (posix "a/b").isUnder (posix "a") = true

-- A `*` matching greedily must still agree with trying every split.
#guard (posix "axxxb").matchGlob "a*b" = true
#guard (posix "ab").matchGlob "a*b" = true
#guard (posix "ab").matchGlob "a*a*b" = false
#guard (posix "aab").matchGlob "a*a*b" = true
#guard (posix "a/b/c").matchGlob "a/**/c" = true
#guard (posix "a/c").matchGlob "a/**/c" = true
#guard (posix "a").matchGlob "**/a" = true
#guard (posix "x/y/a").matchGlob "**/a" = true
#guard (posix "x/y/a").matchGlob "**/b" = false
-- A pattern with many stars against a long name is linear per star, not exponential in their
-- number; this returns promptly rather than hanging.
#guard (posix "logs/------------------------------------------.log").matchGlob
  "logs/*-*-*-*-*-*-*-*-*-*-*-*.txt" = false
#guard ((win "\\\\?\\C:\\a") / (posix "../b")).toWindowsString = "\\\\?\\C:\\b"
#guard ((win "\\\\?\\C:\\a") / (posix "./b")).toWindowsString = "\\\\?\\C:\\a\\b"
-- `..` at the root has nothing to pop and drops out
#guard ((win "\\\\?\\C:\\") / (posix "../../a")).toWindowsString = "\\\\?\\C:\\a"
-- a rooted right operand keeps only the prefix, then folds into it
#guard ((win "\\\\?\\C:\\a\\b") / (win "\\c\\..\\d")).toWindowsString = "\\\\?\\C:\\d"
-- a `.` or `..` the verbatim parser itself produced is an ordinary name and is never folded
#guard ((win "\\\\?\\C:\\a") / (win "\\\\?\\C:\\..\\b")).toWindowsString = "\\\\?\\C:\\..\\b"
-- Only the literal `\\?\` spelling is verbatim. `//?/x` is a device path Windows normalizes like
-- any other, so the parser refuses `?` as a server name rather than canonicalizing it into the
-- verbatim marker: the `.` and `..` here were read as the current and parent directory, and an
-- anchor claiming they are ordinary names would leave `normalize` unable to resolve them.
#guard (win "//?/x/a/./b").isVerbatim = false
#guard (win "//?/x/a/./b").windowsPrefix? = none
#guard (win "//?/x/a/./b").normalize.toWindowsString = "\\?\\x\\a\\b"
-- so a `..` spelled this way no longer walks out of a directory unchecked
#guard (win "//?/C:/uploads/../../../Windows/System32").isUnder (win "\\\\?\\C:\\uploads") = false
-- every other Windows shape is normalized, as Windows normalizes it
#guard (win "\\\\server\\share").isVerbatim = false
#guard (win "\\\\.\\COM42").isVerbatim = false
#guard (win "\\\\.\\COM42\\a\\..\\b").normalize.toWindowsString = "\\\\.\\COM42\\b"
#guard (win "C:\\a").isVerbatim = false
#guard (posix "/a").isVerbatim = false
-- Runs of separators and a trailing separator collapse here as they do in every other path.
#guard (win "\\\\?\\a\\.\\\\b\\").toWindowsString = "\\\\?\\a\\.\\b"
-- the marker itself must be spelled with backslashes; `//?/x` is a path Windows does normalize
#guard (win "//?/x").windowsPrefix? = none
#guard (win "//?/x").toWindowsString = "\\?\\x"
-- A run of separators between the server and the share collapses as it does everywhere else, so the
-- name behind it stays the share instead of becoming the first segment -- which the renderer could
-- not write back, having only one separator to put after a server.
#guard (win "\\\\server\\\\share\\dir").windowsPrefix? == some "\\\\server\\share".toByteArray
#guard (win "//server//share/dir").toWindowsString = "\\\\server\\share\\dir"
#guard (win "\\\\a\\/x").windowsPrefix? == some "\\\\a\\x".toByteArray
#guard (win "\\\\.\\\\pipe\\name").windowsPrefix? == some "\\\\.\\pipe".toByteArray
#guard (win "\\\\?\\UNC\\\\server\\share").windowsPrefix? == some "\\\\?\\UNC\\server\\share".toByteArray
-- a separator run with no name behind it is still just the root
#guard (win "\\\\server\\\\").windowsPrefix? == some "\\\\server".toByteArray
#guard (win "\\\\server\\\\").toWindowsString = "\\\\server\\"
-- the `?` and `.` markers are never re-read as a server name, even with nothing after them
-- `\\?\` names no volume, so it is not a verbatim prefix at all; the `?` is left as a segment,
-- which `isWindowsPortable` then rejects.
#guard (win "\\\\?\\").windowsPrefix? == none
#guard !(win "\\\\?\\").isVerbatim
#guard !(win "\\\\?\\").isAbsolute
#guard (win "\\\\?\\").toWindowsBytes? == none
#guard (win "\\\\.\\").windowsPrefix? == some "\\\\.".toByteArray
#guard (win "\\\\.\\").toWindowsString = "\\\\.\\"
-- joining onto a verbatim path adds the separator the prefix does not carry
#guard ((win "\\\\?\\C:\\foo") / (win "bar")).toWindowsString = "\\\\?\\C:\\foo\\bar"

-- A bare drive letter is the only prefix that leaves the anchor relative, and byte inspection is
-- all it takes to spot one.
#guard Path.Internal.isDrivePrefix "C:".toByteArray = true
#guard Path.Internal.isDrivePrefix "c:".toByteArray = true
#guard Path.Internal.isDrivePrefix "\\\\server\\share".toByteArray = false
#guard Path.Internal.isDrivePrefix "\\\\?\\C:\\foo".toByteArray = false
-- not a drive letter: wrong length, or not a letter
#guard Path.Internal.isDrivePrefix "C:\\".toByteArray = false
#guard Path.Internal.isDrivePrefix "1:".toByteArray = false

-- A prefix that names an absolute location is absolute with no root of its own; a drive letter is
-- not, since `C:foo` is relative to that drive's working directory.
#guard (win "\\\\server\\share").isAbsolute = true
#guard (win "\\\\.\\COM42").isAbsolute = true
#guard (win "\\\\?\\cat_pics").isAbsolute = true
-- every verbatim path is fully qualified, including one that reads as drive-relative
#guard (win "\\\\?\\C:\\foo").isAbsolute = true
#guard (win "\\\\?\\C:foo").isAbsolute = true

-- drive? / root? / anchorBytes across the prefix kinds.
#guard (win "\\\\server\\share").drive? = none
#guard (win "\\\\?\\C:\\foo").drive? = none
-- the root is only present when written out, so these two stay distinct
#guard (win "\\\\server\\share").root? = none
#guard (win "\\\\server\\share").anchorBytes = "\\\\server\\share".toByteArray
#guard (win "\\\\server\\share\\").root? = some "\\".toByteArray
#guard (win "\\\\server\\share\\").anchorBytes = "\\\\server\\share\\".toByteArray
#guard (win "\\\\server\\share\\").toWindowsString = "\\\\server\\share\\"

-- The prefix is the top of the tree: it has no parent, and `..` cannot climb past it.
#guard (win "\\\\server\\share").parent? = none
#guard (win "\\\\server\\share\\").parent? = none
#guard (win "\\\\server\\share\\dir\\f").parent? == some (win "\\\\server\\share\\dir")
#guard (win "\\\\server\\share\\..\\x").normalize == win "\\\\server\\share\\x"
#guard ((win "\\\\server\\share") / (win "..")).normalize == win "\\\\server\\share\\"
-- a drive letter with no root keeps a leading `..`, like any other relative path
#guard (win "C:..\\x").normalize == win "C:..\\x"

-- `relativeTo?` compares whole prefixes, so different shares are unrelatable.
#guard (win "\\\\server\\share\\a").relativeTo? (win "\\\\server\\share\\a\\b") == some (win "b")
#guard (win "\\\\server\\share\\a").relativeTo? (win "\\\\other\\share\\a\\b") = none
#guard (win "C:\\a").relativeTo? (win "\\\\server\\share\\a") = none

-- Rendering to POSIX drops the prefix, as it does for a drive letter.
#guard (win "\\\\server\\share\\x").toPosixString = "/x"

-- Globs ignore the prefix unless asked to match it.
#guard (win "\\\\server\\share\\src\\Main.lean").matchGlob "**/*.lean" = true
#guard (win "\\\\server\\share\\src\\Main.lean").matchGlob "**/*.lean" (matchDrivePrefix := true) = true

end Prefix


-- ---------------------------------------------------------------------------
-- Section: isAbsolute / isRelative
-- ---------------------------------------------------------------------------

section Absolute

#guard (posix "/usr").isAbsolute = true
#guard (posix "usr").isAbsolute = false
#guard (posix "./a").isAbsolute = false
#guard (posix "../a").isAbsolute = false
#guard (posix "/").isAbsolute = true
#guard (win "C:\\foo").isAbsolute = true
#guard (win "C:foo").isAbsolute = false   -- drive-relative (no root)
-- A Windows root with no prefix names the root of whichever drive is current, so it is relative.
#guard (win "\\foo").isAbsolute = false
#guard (win "\\").isAbsolute = false
#guard (win "/foo").isAbsolute = false    -- `/` is just a separator in Windows syntax
#guard (posix "/usr").isRelative = false
#guard (posix "usr").isRelative = true
#guard (win "\\foo").isRelative = true

-- `hasRoot` is the weaker predicate: it holds for the drive-relative paths above, and for a prefix
-- that supplies a root without writing one out.
#guard (posix "/usr").hasRoot = true
#guard (posix "usr").hasRoot = false
#guard (win "\\foo").hasRoot = true
#guard (win "C:\\foo").hasRoot = true
#guard (win "C:foo").hasRoot = false
#guard (win "\\\\server\\share").hasRoot = true
#guard (win "\\\\?\\C:").hasRoot = true

end Absolute


-- ---------------------------------------------------------------------------
-- Section: drive? / root? / anchorBytes
-- ---------------------------------------------------------------------------

section Anchor

#guard (posix "/usr/bin").drive? = none
#guard (posix "/usr/bin").root? = some "/".toByteArray
#guard (posix "/usr/bin").anchorBytes = "/".toByteArray
#guard (posix "a/b").drive? = none
#guard (posix "a/b").root? = none
#guard (posix "a/b").anchorBytes = "".toByteArray
#guard (win "C:\\foo").drive? = some "C:".toByteArray
#guard (win "C:\\foo").root? = some "\\".toByteArray
#guard (win "C:\\foo").anchorBytes = "C:\\".toByteArray
#guard (win "C:foo").drive? = some "C:".toByteArray
#guard (win "C:foo").root? = none
#guard (win "C:foo").anchorBytes = "C:".toByteArray
#guard (win "\\foo").drive? = none
-- Windows treats `c:` and `C:` as one drive, so `==` and `hash` fold the letter's case...
#guard (win "c:\\foo") == win "C:\\foo"
#guard hash (win "c:\\foo") = hash (win "C:\\foo")
-- ...but the bytes are kept as written, so `=` is byte identity and rendering is lossless.
#guard !(decide (win "c:\\foo" = win "C:\\foo"))
#guard (win "c:\\foo").drive? = some "c:".toByteArray
#guard (win "c:\\foo").toWindowsString = "c:\\foo"
-- Every part of a Windows prefix folds, since Windows resolves them all case-insensitively: a
-- verbatim volume and the `UNC` tag included. The bytes are still kept as written.
#guard (win "\\\\?\\c:\\foo") == win "\\\\?\\C:\\foo"
#guard hash (win "\\\\?\\c:\\foo") = hash (win "\\\\?\\C:\\foo")
#guard (win "\\\\?\\c:\\foo").toWindowsString = "\\\\?\\c:\\foo"
#guard (win "\\\\?\\unc\\srv\\shr\\f") == win "\\\\?\\UNC\\srv\\shr\\f"
-- ...but a verbatim path is not the plain path naming the same place: `normalize` treats them
-- differently, so they are not interchangeable.
#guard !((win "\\\\?\\C:\\foo") == win "C:\\foo")
#guard (win "\\foo").root? = some "\\".toByteArray
#guard (win "\\foo").anchorBytes = "\\".toByteArray

end Anchor



-- ---------------------------------------------------------------------------
-- Section: Anchor as the sole carrier of platform flavour
-- ---------------------------------------------------------------------------

section AnchorModel

-- A path with no prefix and no root belongs to neither platform, so the two syntaxes agree on it.
#guard (posix "a/b") == (win "a\\b")
#guard (win "a\\b").anchor == Path.Anchor.neutral
#guard (win "a/b").anchor == Path.Anchor.neutral
#guard (posix "a/b").anchor == Path.Anchor.neutral

-- `Anchor.ofWindows` maps the degenerate combination onto `neutral`, so it is never built.
#guard Path.Anchor.ofWindows none false == Path.Anchor.neutral
#guard Path.Anchor.ofWindows none true == Path.Anchor.windows none true
#guard Path.Anchor.ofWindows (some "C:".toByteArray) false
        == Path.Anchor.windows (some "C:".toByteArray) false

-- An anchor fixes the flavour; the segments below it never do.
#guard (posix "/a/b").anchor == Path.Anchor.posix
#guard (win "C:\\a").anchor == Path.Anchor.windows (some "C:".toByteArray) true
#guard (win "C:a").anchor == Path.Anchor.windows (some "C:".toByteArray) false
#guard (win "\\a").anchor == Path.Anchor.windows none true
#guard (win "\\\\server\\share").anchor
        == Path.Anchor.windows (some "\\\\server\\share".toByteArray) false
#guard (win "\\\\server\\share\\").anchor
        == Path.Anchor.windows (some "\\\\server\\share".toByteArray) true

-- Segments are shared verbatim between flavours.
#guard (posix "/a/./b/..").segments == (win "C:\\a\\.\\b\\..").segments
#guard (posix "/a/b").segments == #[.normal "a".toByteArray, .normal "b".toByteArray]
-- A root carries no segment of its own.
#guard (posix "/").segments == #[]
#guard (win "C:\\").segments == #[]
#guard (win "\\\\server\\share").segments == #[]

-- The anchor alone decides absoluteness, independent of the host platform.
#guard (posix "/a").anchor.isAbsolute
#guard !(win "C:a").anchor.isAbsolute
#guard !(win "\\a").anchor.isAbsolute
#guard (win "\\\\server\\share").anchor.isAbsolute
#guard !Path.Anchor.neutral.isAbsolute

-- A neutral path joins onto an anchor of either flavour, keeping that anchor.
#guard ((posix "/usr") / (posix "lib/x")).toPosixString = "/usr/lib/x"
#guard ((win "C:\\usr") / (posix "lib/x")).toWindowsString = "C:\\usr\\lib\\x"
#guard ((win "C:") / (posix "lib")).toWindowsString = "C:lib"
-- Only a drive letter abuts its first segment; every other prefix is a location in its own right
-- and takes a separator.
#guard ((win "\\\\server\\share") / (posix "a")).toWindowsString = "\\\\server\\share\\a"
#guard ((win "\\\\.\\pipe") / (posix "a")).toWindowsString = "\\\\.\\pipe\\a"
#guard ((win "\\\\?\\cat") / (posix "a")).toWindowsString = "\\\\?\\cat\\a"

-- `..` is dropped only where the anchor has a root above it; a drive-relative anchor keeps it.
#guard (win "C:..").normalize.toWindowsString = "C:.."
#guard (win "C:").normalize.toWindowsString = "C:"
#guard (win "\\..").normalize.toWindowsString = "\\"
#guard (win "\\\\server\\share\\..").normalize.toWindowsString = "\\\\server\\share\\"
#guard (posix "/..").normalize.toPosixString = "/"
#guard (posix "..").normalize.toPosixString = ".."
#guard (posix "a/..").normalize.toPosixString = "."

-- `parent?` walks off the segments and stops at the anchor.
#guard ((win "C:a").parent?.map Path.toWindowsString) = some "C:"
#guard ((win "C:").parent?.map Path.toWindowsString) = none
#guard ((posix "/a").parent?.map Path.toPosixString) = some "/"
#guard ((posix "/").parent?.map Path.toPosixString) = none

-- `startsWith` compares anchors with `==`. A prefix that supplies its own root makes the written
-- separator immaterial, so `\\server\share` and `\\server\share\` are the same anchor — which is
-- what `join` produces, since it has to add that separator before it can put a segment under one.
#guard (posix "/a/b").startsWith (posix "/a")
#guard !(posix "/a/b").startsWith (posix "a")
#guard (win "\\\\server\\share\\a").startsWith (win "\\\\server\\share\\")
#guard (win "\\\\server\\share\\a").startsWith (win "\\\\server\\share")
#guard ((win "\\\\server\\share").join (win "a")).isUnder (win "\\\\server\\share")
-- A bare drive letter supplies no root, so there the separator still separates two anchors.
#guard !(win "C:\\a").startsWith (win "C:")

-- Dropping a prefix leaves an unanchored path, whatever the input flavour was.
#guard ((posix "/a/b").dropPrefix? (posix "/a")).map Path.anchor == some .neutral
#guard ((win "C:\\a\\b").dropPrefix? (win "C:\\a")).map Path.toPosixString == some "b"
#guard ((posix "/a").relativeTo? (posix "/a/b/c")).map Path.anchor == some .neutral

end AnchorModel

-- ---------------------------------------------------------------------------
-- Section: join / /
-- ---------------------------------------------------------------------------

section Join

-- relative appended to relative
#guard ((posix "a/b").join (posix "c/d")).toPosixString = "a/b/c/d"
-- absolute right side replaces left
#guard ((posix "a/b").join (posix "/c")).toPosixString = "/c"
-- join with current-dir segment
#guard ((posix "a").join (posix "./b")).toPosixString = "a/./b"
-- operator alias
#guard ((posix "a/b") / (posix "c")).toPosixString = "a/b/c"
-- joining root onto something
#guard ((posix "/usr") / (posix "local")).toPosixString = "/usr/local"
-- empty second path (empty components → same as first)
#guard ((posix "a/b").join (default : Path)).toPosixString = "a/b"
-- Windows: absolute right replaces left
#guard ((win "C:\\foo").join (win "D:\\bar")).toWindowsString = "D:\\bar"
-- Windows: a right side carrying a prefix replaces the left even when it is drive-relative
#guard ((win "C:\\foo").join (win "D:bar")).toWindowsString = "D:bar"
#guard ((win "C:\\foo").join (win "C:bar")).toWindowsString = "C:bar"
-- Windows: a rooted right side with no prefix is relative to the current drive, so it keeps the
-- left prefix and drops everything else
#guard ((win "C:\\a\\b").join (win "\\c")).toWindowsString = "C:\\c"
#guard ((win "\\\\server\\share\\a").join (win "\\b")).toWindowsString = "\\\\server\\share\\b"
#guard ((win "a\\b").join (win "\\c")).toWindowsString = "\\c"

-- Putting a segment under a prefix that was standing alone writes the root the prefix does not
-- carry; without it the render would read back as a longer prefix instead.
#guard ((win "\\\\server\\share") / (win "a")).toWindowsString = "\\\\server\\share\\a"
#guard ((win "\\\\server\\share") / (win "a")).toWindowsBytes?.isSome
#guard ((win "\\\\.\\COM42") / (win "a")).toWindowsBytes?.isSome
#guard ((win "\\\\?\\C:") / (win "a")).toWindowsBytes?.isSome
-- a bare drive letter is the one prefix a segment may follow directly
#guard ((win "C:") / (win "a")).toWindowsString = "C:a"

end Join


-- ---------------------------------------------------------------------------
-- Section: normalize
-- ---------------------------------------------------------------------------

section Normalize

-- dot eliminated
#guard (posix "a/./b").normalize.toPosixString = "a/b"
-- double-dot resolved
#guard (posix "a/b/../c").normalize.toPosixString = "a/c"
-- double-dot at root clipped
#guard (posix "/a/../..").normalize.toPosixString = "/"
-- multiple dots
#guard (posix "a/b/c/../../d").normalize.toPosixString = "a/d"
-- pure dots stay as "."
#guard (posix ".").normalize.toPosixString = "."
-- relative path normalizing to nothing → "."
#guard (posix "a/..").normalize.toPosixString = "."
-- no-op on clean path
#guard (posix "/usr/local/bin").normalize.toPosixString = "/usr/local/bin"
-- leading ".." in relative path kept
#guard (posix "../../a").normalize.toPosixString = "../../a"
-- trailing dot
#guard (posix "a/b/.").normalize.toPosixString = "a/b"
-- Windows: normalize resolves .. across drive-rooted path
#guard (win "C:\\a\\..\\b").normalize.toWindowsString = "C:\\b"
-- Windows drive-relative: a leading ".." is preserved (the path is relative to the drive's cwd)
#guard (win "C:..").normalize.toWindowsString = "C:.."
#guard (win "C:..\\a").normalize.toWindowsString = "C:..\\a"
-- Windows drive-rooted: ".." above the root is dropped
#guard (win "C:\\..").normalize.toWindowsString = "C:\\"
-- empty default path normalizes to "."
#guard (default : Path).normalize.toPosixString = "."
-- normalize is idempotent
#guard (posix "a/b/c/../../d").normalize.normalize.toPosixString =
       (posix "a/b/c/../../d").normalize.toPosixString
#guard (posix "/a/../..").normalize.normalize.toPosixString =
       (posix "/a/../..").normalize.toPosixString

-- A relative path that normalizes to nothing keeps no segment standing in for the working
-- directory: it still renders as ".", but it no longer reads as one directory deep, which is what
-- `startsWith` and `relativeTo?` build on.
#guard (posix ".").normalize.segments.isEmpty
#guard (posix "a/..").normalize.segments.isEmpty
#guard (posix "a/b").isUnder (posix ".")
#guard (posix "./a").isUnder (posix ".")
#guard (posix "a/../b").isUnder (posix "a/..")
#guard (posix "/safe/../etc").isUnder (posix "/safe") = false

end Normalize


-- ---------------------------------------------------------------------------
-- Section: parent
-- ---------------------------------------------------------------------------

section Parent

-- typical case
#guard (posix "/a/b/c").parent?.map (·.toPosixString) = some "/a/b"
-- one level from root
#guard (posix "/a").parent?.map (·.toPosixString) = some "/"
-- root has no parent
#guard (posix "/").parent? = none
-- relative single segment → "."
#guard (posix "a").parent?.map (·.toPosixString) = some "."
-- relative two segments
#guard (posix "a/b").parent?.map (·.toPosixString) = some "a"
-- "." names the working directory itself, so it has no parent
#guard (posix ".").parent? = none
#guard (posix ".").isCurrentDir
#guard !(posix "a").isCurrentDir
#guard !(posix "./a").isCurrentDir
#guard !(posix "/").isCurrentDir
-- ".." parent
#guard (posix "..").parent?.map (·.toPosixString) = some "."
-- A trailing `.` is not a component of its own: it goes with the name it stands on, so `"a/b/."`
-- has the same parent as `"a/b"`.
#guard (posix "a/.").parent?.map (·.toPosixString) = some "."
#guard (posix "a/b/.").parent?.map (·.toPosixString) = some "a"
#guard (posix "a/b/c/.").parent?.map (·.toPosixString) = some "a/b"
#guard (posix "a/./.").parent?.map (·.toPosixString) = some "."
#guard (posix "/a/.").parent?.map (·.toPosixString) = some "/"
#guard (posix "/.").parent? = none
-- `"./."` names the working directory, like `"."`, so it has no parent either
#guard (posix "./.").parent? = none
-- ".." is a component: it is dropped, not resolved
#guard (posix "a/b/..").parent?.map (·.toPosixString) = some "a/b"
#guard (posix "a/b/../.").parent?.map (·.toPosixString) = some "a/b"
#guard (posix "../.").parent?.map (·.toPosixString) = some "."
-- an interior `.` is left as written
#guard (posix "a/./b").parent?.map (·.toPosixString) = some "a/."
-- `parent?` and `filename?` read the same components, so they compose
#guard (posix "a/b/.").parent?.map (·.toPosixString) = some "a"
#guard (posix "a/b/.").filename? = some (Path.Filename.mk "b".toByteArray)
#guard (posix "a/b/c/.").parents.toList.map (·.toPosixString) = ["a/b", "a", "."]
-- empty path has no parent
#guard (default : Path).parent? = none
-- Windows drive-relative: parent of "C:foo" is the bare drive "C:"
#guard (win "C:foo").parent?.map (·.toWindowsString) = some "C:"

end Parent


-- ---------------------------------------------------------------------------
-- Section: parents iterator
-- ---------------------------------------------------------------------------

section ParentsIter

private def collectParents (p : Path) : List String :=
  p.parents.toList.map (·.toPosixString)

#guard collectParents (posix "/a/b/c") = ["/a/b", "/a", "/"]
#guard collectParents (posix "a/b/c")  = ["a/b", "a", "."]
#guard collectParents (posix "/")      = []
#guard collectParents (posix "a")      = ["."]
-- path with leading ".." components: each ".." is its own parent step
#guard collectParents (posix "../../a") = ["../..", "..", "."]

end ParentsIter


-- ---------------------------------------------------------------------------
-- Section: filename? / fileStem? / extension? / hasExtension
-- ---------------------------------------------------------------------------

section FileInfo

-- filename?
#guard (posix "/usr/local/bin/lean").filename? = some (Path.Filename.mk "lean".toByteArray)
#guard (posix "archive.tar.gz").filename? = some (Path.Filename.mk "archive.tar.gz".toByteArray)
#guard (posix "/").filename? = none
#guard (posix "a/..").filename? = none
#guard (default : Path).filename? = none
-- a trailing `.` names the same entry as the segment before it
#guard (posix "a/.").filename? = some (Path.Filename.mk "a".toByteArray)
#guard (posix "a/b.txt/./.").filename? = some (Path.Filename.mk "b.txt".toByteArray)
#guard (posix ".").filename? = none
#guard (posix "./.").filename? = none
#guard (posix "a/../.").filename? = none
#guard (posix "a/b.txt/.").extension? = some (Path.Extension.mk "txt".toByteArray)
#guard (posix "a/.hidden/.").isHidden = true
#guard ((posix "a/b/.").setFilename (Path.Filename.mk "d".toByteArray)).toPosixString = "a/d"

-- fileStem?
#guard (posix "Main.lean").fileStem? = some (Path.Filename.mk "Main".toByteArray)
#guard (posix "archive.tar.gz").fileStem? = some (Path.Filename.mk "archive.tar".toByteArray)
#guard (posix "Makefile").fileStem? = some (Path.Filename.mk "Makefile".toByteArray)
#guard (posix ".gitignore").fileStem? = some (Path.Filename.mk ".gitignore".toByteArray)
#guard (posix ".hidden.lean").fileStem? = some (Path.Filename.mk ".hidden".toByteArray)
#guard (posix "/").fileStem? = none
-- the stem round-trips into its setter with no re-validation
#guard ((posix "a/archive.tar.gz").withFileStem (posix "b.md").fileStem?.get!).toPosixString = "a/b.gz"

-- extension?
#guard (posix "Main.lean").extension? = some (Path.Extension.mk "lean".toByteArray)
#guard (posix "archive.tar.gz").extension? = some (Path.Extension.mk "gz".toByteArray)
#guard (posix "Makefile").extension? = none
#guard (posix ".gitignore").extension? = none
#guard (posix ".hidden.lean").extension? = some (Path.Extension.mk "lean".toByteArray)
#guard (posix "/").extension? = none

-- `removeExtension` strips any `.` past the first byte, which need not be one `hasExtension` sees:
-- an empty extension is one no `Extension` can hold.
#guard (posix "a.").hasExtension = false
#guard (posix "a.").removeExtension.toPosixString = "a"
#guard (posix "a.b.").removeExtension.toPosixString = "a.b"
-- hasExtension
#guard (posix "foo.txt").hasExtension = true
#guard (posix "Makefile").hasExtension = false
#guard (posix ".gitignore").hasExtension = false
#guard (posix "/").hasExtension = false

-- isHidden
#guard (posix ".gitignore").isHidden = true
#guard (posix "a/.hidden").isHidden = true
#guard (posix "foo.txt").isHidden = false
#guard (posix "Makefile").isHidden = false
#guard (posix "/").isHidden = false  -- no file name
#guard (Path.Filename.mk ".gitignore".toByteArray).isHidden = true
#guard (Path.Filename.mk "foo".toByteArray).isHidden = false

end FileInfo


-- ---------------------------------------------------------------------------
-- Section: Filename.ofString? / ofString! / Extension.ofString? / ofString!
-- ---------------------------------------------------------------------------

section OfString

-- Filename.ofString?
#guard Path.Filename.ofString? "lean" = some (Path.Filename.mk "lean".toByteArray)
#guard Path.Filename.ofString? "" = none
#guard Path.Filename.ofString? "." = none
#guard Path.Filename.ofString? ".." = none
#guard Path.Filename.ofString? "a/b" = none
#guard Path.Filename.ofString? "a\\b" = none
#guard Path.Filename.ofString? "a\x00b" = none

-- Filename.ofString!
#guard Path.Filename.ofString! "lean" = Path.Filename.mk "lean".toByteArray

-- Extension.ofString?
#guard Path.Extension.ofString? "lean" = some (Path.Extension.mk "lean".toByteArray)
#guard Path.Extension.ofString? "" = none
#guard Path.Extension.ofString? "a.b" = none
#guard Path.Extension.ofString? "a/b" = none
#guard Path.Extension.ofString? "a\\b" = none
#guard Path.Extension.ofString? "a\x00b" = none

-- Extension.ofString!
#guard Path.Extension.ofString! "lean" = Path.Extension.mk "lean".toByteArray

end OfString


-- ---------------------------------------------------------------------------
-- Section: suffixes / withFilePrefix / withFileStem
-- ---------------------------------------------------------------------------

section Suffixes

#guard (posix "archive.tar.gz").suffixes =
       #[Path.Extension.mk "tar".toByteArray, Path.Extension.mk "gz".toByteArray]
#guard (posix "foo.txt").suffixes = #[Path.Extension.mk "txt".toByteArray]
#guard (posix "Makefile").suffixes = #[]
#guard (posix ".gitignore").suffixes = #[]
#guard (posix ".hidden.tar.gz").suffixes =
       #[Path.Extension.mk "tar".toByteArray, Path.Extension.mk "gz".toByteArray]
#guard (posix "/").suffixes = #[]
-- a doubled or trailing dot yields an empty piece, which no `Extension` can hold and `extension?`
-- already reports as absent
#guard (posix "a..b").suffixes = #[Path.Extension.mk "b".toByteArray]
#guard (posix "a.b.").suffixes = #[Path.Extension.mk "b".toByteArray]
#guard (posix "a.b.").extension? = none

-- withFilePrefix: keeps every extension
#guard ((posix "a/archive.tar.gz").withFilePrefix (Path.Filename.mk "backup".toByteArray)).toPosixString = "a/backup.tar.gz"
#guard ((posix "a/foo.txt").withFilePrefix (.mk "bar".toByteArray)).toPosixString = "a/bar.txt"
#guard ((posix "a/Makefile").withFilePrefix (.mk "GNUmakefile".toByteArray)).toPosixString = "a/GNUmakefile"
-- invariant: suffixes unchanged
#guard ((posix "archive.tar.gz").withFilePrefix (Path.Filename.mk "backup".toByteArray)).suffixes =
       (posix "archive.tar.gz").suffixes
-- the prefix round-trips into its setter with no re-validation
#guard ((posix "a/archive.tar.gz").withFilePrefix (posix "b").filePrefix?.get!).toPosixString =
       "a/b.tar.gz"

-- withFileStem: keeps only the last extension
#guard ((posix "a/archive.tar.gz").withFileStem (.mk "backup".toByteArray)).toPosixString = "a/backup.gz"
#guard ((posix "a/foo.txt").withFileStem (.mk "bar".toByteArray)).toPosixString = "a/bar.txt"
#guard ((posix "a/Makefile").withFileStem (.mk "GNUmakefile".toByteArray)).toPosixString = "a/GNUmakefile"
-- no file name to replace
#guard ((posix "/").withFileStem (.mk "x".toByteArray)).toPosixString = "/"
#guard ((posix "a/..").withFilePrefix (.mk "x".toByteArray)).toPosixString = "a/.."

-- dotfile: the whole name is the prefix and the stem alike, so both setters replace it entirely
#guard ((posix ".gitignore").withFilePrefix (.mk "profile".toByteArray)).toPosixString = "profile"
#guard ((posix ".gitignore").withFileStem (.mk "profile".toByteArray)).toPosixString = "profile"
-- dotfile: withExtension appends since the stem is the whole name and there's no extension
#guard ((posix ".gitignore").withExtension (.mk "bak".toByteArray)).toPosixString = ".gitignore.bak"

end Suffixes


-- ---------------------------------------------------------------------------
-- Section: setFilename / withExtension / addExtension
-- ---------------------------------------------------------------------------

section Modification

-- setFilename
#guard ((posix "a/b/c").setFilename (Path.Filename.mk "d".toByteArray)).toPosixString = "a/b/d"
#guard ((posix "/").setFilename (Path.Filename.mk "d".toByteArray)).toPosixString = "/"  -- no-op on root
#guard ((posix "a/..").setFilename (Path.Filename.mk "d".toByteArray)).toPosixString = "a/.."  -- no-op on parent component
-- single-segment relative path: result has no parent prefix
#guard ((posix "foo").setFilename (Path.Filename.mk "bar".toByteArray)).toPosixString = "bar"

-- withExtension
#guard ((posix "a/b.tar.gz").withExtension (Path.Extension.mk "xz".toByteArray)).toPosixString = "a/b.tar.xz"
#guard ((posix "a/b.txt").withExtension (Path.Extension.mk "lean".toByteArray)).toPosixString = "a/b.lean"
#guard ((posix "a/Makefile").withExtension (Path.Extension.mk "bak".toByteArray)).toPosixString = "a/Makefile.bak"
#guard ((posix "/").withExtension (Path.Extension.mk "bak".toByteArray)).toPosixString = "/"  -- no-op

-- addExtension
#guard ((posix "a/b.tar.gz").addExtension (Path.Extension.mk "bak".toByteArray)).toPosixString = "a/b.tar.gz.bak"
#guard ((posix "a/Makefile").addExtension (Path.Extension.mk "bak".toByteArray)).toPosixString = "a/Makefile.bak"
#guard ((posix "/").addExtension (Path.Extension.mk "bak".toByteArray)).toPosixString = "/"  -- no-op

-- removeExtension
#guard ((posix "a/b.tar.gz").removeExtension).toPosixString = "a/b.tar"  -- only the last extension
#guard ((posix "a/b.txt").removeExtension).toPosixString = "a/b"
#guard ((posix "a/Makefile").removeExtension).toPosixString = "a/Makefile"  -- no extension: no-op
#guard ((posix ".gitignore").removeExtension).toPosixString = ".gitignore"  -- dotfile: no-op
#guard ((posix ".hidden.lean").removeExtension).toPosixString = ".hidden"
#guard ((posix "/").removeExtension).toPosixString = "/"  -- no file name: no-op
-- inverse of addExtension
#guard ((posix "a/b.txt").addExtension (Path.Extension.mk "bak".toByteArray) |>.removeExtension).toPosixString = "a/b.txt"

end Modification


-- ---------------------------------------------------------------------------
-- Section: `.` is not a component
-- ---------------------------------------------------------------------------

section Components

-- `components` drops every `.` and keeps everything else, `..` included.
#guard (posix "a/./b").components = #[.normal "a".toByteArray, .normal "b".toByteArray]
#guard (posix "./a/././b/.").components = #[.normal "a".toByteArray, .normal "b".toByteArray]
#guard (posix "a/../b").components
  = #[.normal "a".toByteArray, .parent, .normal "b".toByteArray]
#guard (posix ".").components = #[]
#guard (posix "./.").components = #[]
#guard (posix "/").components = #[]
#guard Path.empty.components = #[]
-- inside a verbatim path `.` is an ordinary name, so it is a component like any other
#guard (win "\\\\?\\C:\\a\\.\\b").components
  = #[.normal "a".toByteArray, .normal ".".toByteArray, .normal "b".toByteArray]

-- A `.` is kept in `segments`, so rendering is still lossless.
#guard (posix "a/./b").toPosixString = "a/./b"
#guard (posix "a/.").toPosixString = "a/."

-- `==`, `compare`, and `hash` all read the components, so a `.` never separates two paths.
#guard (posix "a/./b") == (posix "a/b")
#guard compare (posix "a/./b") (posix "a/b") = .eq
#guard hash (posix "a/./b") == hash (posix "a/b")
#guard (posix "a/b/.") == (posix "a/b")
#guard (posix ".") == Path.empty
#guard hash (posix ".") == hash Path.empty
#guard (posix "/usr/./bin") == (posix "/usr/bin")
-- but `=` is still byte identity, which is what keeps rendering faithful
#guard !(decide ((posix "a/./b") = (posix "a/b")))
-- `..` is a component, so it does separate them
#guard !((posix "a/../b") == (posix "b"))
#guard !((posix "a/..") == (posix "."))

-- The same rule reaches every operation that asks what a path names.
#guard (posix "a/b/.").filename? = some (Path.Filename.mk "b".toByteArray)
#guard (posix "a/./b").parent?.map (·.toPosixString) = some "a/."
#guard (posix "/usr/bin/.").endsWith (posix "bin")
#guard (posix "/usr/./bin").startsWith (posix "/usr")
#guard (posix "/usr/./bin").startsWith (posix "/usr/bin")
#guard ((posix "a/./b/c").dropPrefix? (posix "a/b")).map (·.toPosixString) = some "c"
#guard ((posix "a/.").dropPrefix? (posix "a")).map (·.toPosixString) = some "."
#guard (posix "a/./b").matchGlob "a/b"
#guard (posix "a/./b").matchGlob "a/*"
#guard (posix ".").matchGlob "."
#guard Path.empty.matchGlob "."
#guard (posix "/.").isRoot
#guard (posix "./.").isCurrentDir
#guard Path.empty.isCurrentDir
#guard ((posix "a/./b").relativeTo? (posix "a/c")).map (·.toPosixString) = some "../c"

-- `isEmpty` is the one question about the representation rather than the location, so it still
-- separates the paths that `==` identifies.
#guard (posix ".").isEmpty = false
#guard Path.empty.isEmpty = true

-- Paths are usable as keys: two spellings of one path land on one entry.
#guard (Std.HashMap.emptyWithCapacity.insert (posix "a/./b") 1 |>.insert (posix "a/b") 2).size = 1

end Components


-- ---------------------------------------------------------------------------
-- Section: startsWith / endsWith
-- ---------------------------------------------------------------------------

section StartEnd

#guard (posix "/usr/local/bin").startsWith (posix "/usr/local") = true
#guard (posix "/usr/local/bin").startsWith (posix "/usr") = true
#guard (posix "/usr/local/bin").startsWith (posix "/usr/local/bin") = true
-- not a component-wise prefix
#guard (posix "/usr/local/bin").startsWith (posix "/us") = false
-- relative prefixes
#guard (posix "a/b/c").startsWith (posix "a/b") = true
#guard (posix "a/b/c").startsWith (posix "a") = true
#guard (posix "a/b/c").startsWith (posix "b") = false

#guard (posix "/usr/local/bin").endsWith (posix "local/bin") = true
#guard (posix "/usr/local/bin").endsWith (posix "bin") = true
#guard (posix "/usr/local/bin").endsWith (posix "/usr/local/bin") = true
-- a relative suffix matches whole components from the back, even just behind the root
#guard (posix "/usr/local/bin").endsWith (posix "usr/local/bin") = true
#guard (posix "/a").endsWith (posix "a") = true
-- but the match is component-wise, not a substring
#guard (posix "/usr/local/bin").endsWith (posix "sr/bin") = false
-- an absolute suffix must line up with the root
#guard (posix "/usr/local/bin").endsWith (posix "/bin") = false
#guard (posix "a/b/c").endsWith (posix "b/c") = true
#guard (posix "a/b/c").endsWith (posix "a") = false
-- a path ends with itself
#guard (posix "a/b/c").endsWith (posix "a/b/c") = true
#guard (posix "a").endsWith (posix "a") = true
#guard (posix "/a").endsWith (posix "/a") = true
#guard (win "C:\\a").endsWith (win "C:\\a") = true
-- a suffix longer than the path never matches
#guard (posix "bin").endsWith (posix "local/bin") = false

end StartEnd


-- ---------------------------------------------------------------------------
-- Section: dropPrefix?
-- ---------------------------------------------------------------------------

section DropPrefix

#guard ((posix "/usr/local/bin").dropPrefix? (posix "/usr")).map (·.toPosixString) = some "local/bin"
-- nothing left below the prefix: the path has no segments and renders as ".", never as "",
-- which no parser would read back
#guard ((posix "/usr/local/bin").dropPrefix? (posix "/usr/local/bin")).map (·.toPosixString) = some "."
#guard (posix "/usr/local/bin").dropPrefix? (posix "/etc") = none
#guard ((posix "a/b/c").dropPrefix? (posix "a/b")).map (·.toPosixString) = some "c"
-- not a prefix
#guard (posix "a/b/c").dropPrefix? (posix "b") = none
-- prefix longer than path → none
#guard (posix "a/b").dropPrefix? (posix "a/b/c") = none

end DropPrefix


-- ---------------------------------------------------------------------------
-- Section: relativeTo?
-- ---------------------------------------------------------------------------

section RelativeTo

-- same directory → a relative path with no segments, rendering as "."; join with base gives base
#guard ((posix "/a/b").relativeTo? (posix "/a/b")).map (·.toPosixString) = some "."
-- sibling file
#guard ((posix "/a/b").relativeTo? (posix "/a/c")).map (·.toPosixString) = some "../c"
-- deeper target
#guard ((posix "/a").relativeTo? (posix "/a/b/c")).map (·.toPosixString) = some "b/c"
-- going up
#guard ((posix "/a/b/c").relativeTo? (posix "/a")).map (·.toPosixString) = some "../.."
-- completely different trees
#guard ((posix "/a/b").relativeTo? (posix "/c/d")).map (·.toPosixString) = some "../../c/d"
-- absolute vs relative → none
#guard (posix "/a/b").relativeTo? (posix "a/b") = none
-- both relative
#guard ((posix "a/b").relativeTo? (posix "a/c")).map (·.toPosixString) = some "../c"
-- Windows: different drive → none
#guard (win "C:\\foo").relativeTo? (win "D:\\foo") = none
-- Windows: drive-rooted and cwd-relative paths have different anchors
#guard (win "\\a").relativeTo? (win "b") = none
#guard ((win "\\a").relativeTo? (win "\\b")).map (·.toWindowsString) = some "..\\b"
-- a POSIX root and a Windows root are different anchors too
#guard (posix "/a").relativeTo? (win "\\b") = none

-- documented invariant: `(base.join r).normalize = target.normalize`
private def relInvariant (base target : Path) : Bool :=
  match base.relativeTo? target with
  | none => false
  | some r => (base.join r).normalize == target.normalize
#guard relInvariant (posix "/a/b") (posix "/a/c")
#guard relInvariant (posix "/a") (posix "/a/b/c")
#guard relInvariant (posix "/a/b/c") (posix "/a")
#guard relInvariant (posix "/a/b") (posix "/c/d")
#guard relInvariant (posix "/a/b") (posix "/a/b")
#guard relInvariant (posix "a/b") (posix "a/c")

-- `.` names no directory, so it is neither ascended out of nor emitted. `normalize` produces
-- exactly this base, so the invariant has to hold for it.
#guard ((posix ".").relativeTo? (posix "a/c")).map (·.toPosixString) = some "a/c"
#guard relInvariant (posix ".") (posix "a/c")
#guard relInvariant (posix "a/..").normalize (posix "b")
#guard ((posix "./x").relativeTo? (posix "./x/y")).map (·.toPosixString) = some "y"
#guard ((posix "/a/./b").relativeTo? (posix "/a/c")).map (·.toPosixString) = some "../c"
-- a `..` in `base` that `target` does not share names a directory nothing can lead back into
#guard (posix "..").relativeTo? (posix "c") = none
#guard (posix "a/../..").relativeTo? (posix "b") = none
#guard ((posix "../a").relativeTo? (posix "../b")).map (·.toPosixString) = some "../b"

end RelativeTo


-- ---------------------------------------------------------------------------
-- Section: matchGlob
-- ---------------------------------------------------------------------------

-- matchGlob is syntactic, like `startsWith` and unlike `isUnder`: no `.` or `..` is resolved first.
#guard (posix "uploads/../secret").matchGlob "uploads/**"
#guard (posix "uploads/../secret").isUnder (posix "uploads") = false

section Glob

-- exact match
#guard (posix "src/Main.lean").matchGlob "src/Main.lean" = true
-- * wildcard within a segment
#guard (posix "src/Main.lean").matchGlob "src/*.lean" = true
#guard (posix "src/Main.lean").matchGlob "src/*.txt" = false
-- * does not cross segment boundaries
#guard (posix "src/sub/Main.lean").matchGlob "src/*.lean" = false
-- ** matches zero segments
#guard (posix "src/Main.lean").matchGlob "**/Main.lean" = true
-- ** matches multiple segments
#guard (posix "a/b/c/Main.lean").matchGlob "**/Main.lean" = true
-- ** matches across root-level
#guard (posix "/a/b/foo.lean").matchGlob "**/*.lean" = true
-- ? wildcard
#guard (posix "src/ab.lean").matchGlob "src/??.lean" = true
#guard (posix "src/abc.lean").matchGlob "src/??.lean" = false
-- character class
#guard (posix "src/a.lean").matchGlob "src/[abc].lean" = true
#guard (posix "src/d.lean").matchGlob "src/[abc].lean" = false
-- character range
#guard (posix "src/b.lean").matchGlob "src/[a-z].lean" = true
#guard (posix "src/B.lean").matchGlob "src/[a-z].lean" = false
-- negated class
#guard (posix "src/d.lean").matchGlob "src/[!abc].lean" = true
#guard (posix "src/a.lean").matchGlob "src/[!abc].lean" = false
-- no match on wrong depth without **
#guard (posix "a/b/c").matchGlob "a/b" = false
-- ** matching zero segments
#guard (posix "foo.lean").matchGlob "**/*.lean" = true
-- ** in the middle: matches multiple segments between fixed anchors
#guard (posix "a/b/c/d").matchGlob "a/**/d" = true
-- ** in the middle: matches zero segments between fixed anchors
#guard (posix "a/d").matchGlob "a/**/d" = true
-- ** on absolute path with single non-root segment (must skip the "" root component)
#guard (posix "/foo.lean").matchGlob "**/foo.lean" = true
-- a syntactically invalid pattern (unterminated character class) matches nothing...
#guard (posix "src/a.lean").matchGlob "src/[abc" = false
-- ...including the empty path (regression: a parse failure must not match everything)
#guard Path.empty.matchGlob "[abc" = false
-- ...and even when the leftover after the unterminated class would otherwise match (the pattern
-- must be rejected wholesale, not parsed up to the bad `[`).
#guard (posix "a").matchGlob "a[bc" = false
#guard (posix "abc").matchGlob "abc[x" = false
#guard (posix "a/b").matchGlob "a/b[x" = false
-- an unterminated class in a non-final segment is likewise rejected
#guard (posix "a/b").matchGlob "a[/b" = false
-- matchGlob reads the path's components, so a `.` is not matched against a segment of the pattern;
-- a `..` is a component and is matched as written rather than resolved.
#guard (posix "a/./b").matchGlob "a/b" = true
#guard (posix "a/./b").matchGlob "a/*/b" = false
#guard (posix "a/../b").matchGlob "a/*/b" = true
#guard (posix "a/../b").matchGlob "b" = false
-- by default, a Windows drive prefix is ignored: a generic pattern matches without mentioning it,
-- and a pattern that does mention it fails (the drive component isn't there to match against)
#guard (win "C:\\Users\\foo").matchGlob "**/Users/foo" = true
#guard (win "C:\\Users\\foo").matchGlob "C:/**/Users/foo" = false
-- matchDrivePrefix := true instead requires the drive to appear as its own leading segment
#guard (win "C:\\Users\\foo").matchGlob "C:/**/Users/foo" (matchDrivePrefix := true) = true
#guard (win "C:\\Users\\foo").matchGlob "**/Users/foo" (matchDrivePrefix := true) = true
#guard (win "D:\\Users\\foo").matchGlob "C:/**/Users/foo" (matchDrivePrefix := true) = false
-- Under matchDrivePrefix the prefix *is* the leading segment, so an absolute path takes a single
-- separator after it: emitting the root's empty segment as well would demand the doubled "C://a".
#guard (win "C:\\a").matchGlob "C:/a" (matchDrivePrefix := true) = true
#guard (win "C:\\a\\b").matchGlob "C:/a/b" (matchDrivePrefix := true) = true
#guard (win "C:\\").matchGlob "C:" (matchDrivePrefix := true) = true
#guard (win "\\\\server\\share\\a").matchGlob "\\\\server\\share/a" (matchDrivePrefix := true) = true
-- A root is the only thing the pattern language cannot tell from its absence once a prefix stands
-- in the leading segment, so the drive-relative path matches the same pattern.
#guard (win "C:a").matchGlob "C:/a" (matchDrivePrefix := true) = true

-- Every separator in a pattern counts. A path is parsed with its repeated and trailing separators
-- collapsed, so a pattern that spells one names a segment no path has and matches nothing.
#guard (posix "/").matchGlob "/" = true
#guard (posix "/usr").matchGlob "/usr" = true
#guard (posix "/x").matchGlob "//x" = false
#guard (posix "a/b").matchGlob "a/b/" = false
#guard (posix "a/b").matchGlob "a//b" = false
#guard (posix "a/b/").segments.size = 2
-- A path is matched as its rendering split back on `/`, so a root writes an empty leading segment,
-- and a bare root, whose whole rendering is `"/"`, writes one on either side of it.
#guard (posix "/").matchGlob "/*" = true
#guard (posix "/x").matchGlob "/*" = true
#guard (posix "/").matchGlob "/**" = true
#guard (posix "x").matchGlob "/x" = false

-- `**` is a segment of its own or a syntax error: reading `a**b` as `a*b` would hand back a weaker
-- pattern than the one written.
#guard (posix "axb").matchGlob "a**b" = false
#guard (posix "xa").matchGlob "**a" = false
#guard (posix "a/xb").matchGlob "a/**b" = false
#guard (posix "a/b").matchGlob "a/***" = false
-- A `**` before a further segment matches zero or more of them, but a trailing one has to take a
-- segment of its own: the `/` written before it still has to be there.
#guard (posix "a/c").matchGlob "a/**/c" = true
#guard (posix "a").matchGlob "a/**" = false
#guard (posix "a/b").matchGlob "a/**" = true
#guard (posix "a").matchGlob "**" = true
-- A `**` takes the separator after it with it, so `a/**/` is `a/**`.
#guard (posix "a").matchGlob "a/**/" = false
#guard (posix "a/b").matchGlob "a/**/" = true
#guard (posix "a").matchGlob "**/" = true

-- A `]` right after `[` or `[!` is an ordinary member, so a class can hold one...
#guard (posix "]").matchGlob "[]]" = true
#guard (posix "a").matchGlob "[]a]" = true
#guard (posix "]").matchGlob "[]a]" = true
#guard (posix "a").matchGlob "[!]]" = true
#guard (posix "]").matchGlob "[!]]" = false
-- ...and `[]` and `[!]` are unterminated rather than empty classes.
#guard (posix "x").matchGlob "[]" = false
#guard (posix "a").matchGlob "[!]" = false

-- Case-insensitive matching folds ASCII letters on both sides of the comparison.
#guard (posix "src/MAIN.lean").matchGlob "src/main.lean" = false
#guard (posix "src/MAIN.lean").matchGlob "src/main.lean" (caseInsensitive := true) = true
#guard (posix "SRC/Main.LEAN").matchGlob "src/*.lean" (caseInsensitive := true) = true
#guard (posix "SRC/x/Main.lean").matchGlob "src/**/main.lean" (caseInsensitive := true) = true
#guard (posix "src/AB.lean").matchGlob "src/??.lean" (caseInsensitive := true) = true
-- A class member folds like a literal...
#guard (posix "src/B.lean").matchGlob "src/[abc].lean" (caseInsensitive := true) = true
#guard (posix "src/D.lean").matchGlob "src/[abc].lean" (caseInsensitive := true) = false
-- ...and so does a negated one, so the excluded letter is excluded in either case.
#guard (posix "src/A.lean").matchGlob "src/[!abc].lean" (caseInsensitive := true) = false
#guard (posix "src/a.lean").matchGlob "src/[!ABC].lean" (caseInsensitive := true) = false
#guard (posix "src/d.lean").matchGlob "src/[!ABC].lean" (caseInsensitive := true) = true
-- A range is tested against the character in both ASCII cases, so it need not be written in the
-- case that appears in the path.
#guard (posix "src/B.lean").matchGlob "src/[a-z].lean" (caseInsensitive := true) = true
#guard (posix "src/b.lean").matchGlob "src/[A-Z].lean" (caseInsensitive := true) = true
#guard (posix "src/B.lean").matchGlob "src/[!a-z].lean" (caseInsensitive := true) = false
-- Folding the character rather than the range's endpoints keeps a range that spans non-letters
-- meaningful: `[@-B]` still holds `@`, and it holds `a` because `A` is in it.
#guard (posix "@").matchGlob "[@-B]" (caseInsensitive := true) = true
#guard (posix "A").matchGlob "[@-B]" (caseInsensitive := true) = true
#guard (posix "a").matchGlob "[@-B]" (caseInsensitive := true) = true
#guard (posix "a").matchGlob "[@-B]" = false
-- Folding is ASCII-only, so a non-ASCII letter matches only as written.
#guard (posix "\u00c9").matchGlob "\u00e9" (caseInsensitive := true) = false
#guard (posix "\u00c9").matchGlob "\u00c9" (caseInsensitive := true) = true
-- A Windows prefix is a segment like any other, so it folds too.
#guard (win "c:\\a").matchGlob "C:/a" (matchDrivePrefix := true) = false
#guard (win "c:\\a").matchGlob "C:/a" (matchDrivePrefix := true) (caseInsensitive := true) = true
-- Folding never applies to the separator, so it cannot make `*` cross a segment boundary.
#guard (posix "a/b").matchGlob "a*b" (caseInsensitive := true) = false

end Glob


-- ---------------------------------------------------------------------------
-- Section: empty / isEmpty
-- ---------------------------------------------------------------------------

section EmptyPath

-- empty has no anchor and no segments
#guard Path.empty.anchor == Path.Anchor.neutral
#guard Path.empty.segments = #[]
-- isEmpty on empty
#guard Path.empty.isEmpty = true
-- Inhabited default is also empty
#guard (default : Path).isEmpty = true
-- non-empty paths
#guard (posix "a").isEmpty = false
#guard (posix "/").isEmpty = false
#guard (posix ".").isEmpty = false
-- joining empty with a path gives that path
#guard (Path.empty.join (posix "a/b")).toPosixString = "a/b"
-- joining a path with empty gives that path
#guard ((posix "a/b").join Path.empty).toPosixString = "a/b"

end EmptyPath


-- ---------------------------------------------------------------------------
-- Section: isRoot
-- ---------------------------------------------------------------------------

section IsRoot

-- POSIX root
#guard (posix "/").isRoot = true
-- Windows drive root
#guard (win "C:\\").isRoot = true
-- Windows root without drive: a root path, though not an absolute one
#guard (win "\\").isRoot = true
#guard (win "\\").isAbsolute = false
-- absolute but not root (has normal components)
#guard (posix "/usr").isRoot = false
#guard (win "C:\\foo").isRoot = false
-- relative paths are never root
#guard (posix "a").isRoot = false
#guard (posix ".").isRoot = false
-- empty path is not root
#guard Path.empty.isRoot = false

end IsRoot

-- ---------------------------------------------------------------------------
-- Section: filePrefix?
-- ---------------------------------------------------------------------------

section FilePrefix

-- removes everything from first dot
#guard (posix "foo.tar.gz").filePrefix? = some (Path.Filename.mk "foo".toByteArray)
-- single extension
#guard (posix "foo.txt").filePrefix? = some (Path.Filename.mk "foo".toByteArray)
-- no extension: whole name is the prefix
#guard (posix "Makefile").filePrefix? = some (Path.Filename.mk "Makefile".toByteArray)
-- leading-dot file with no extension: whole name preserved
#guard (posix ".gitignore").filePrefix? = some (Path.Filename.mk ".gitignore".toByteArray)
-- leading-dot file with extension: leading dot kept, rest up to first dot
#guard (posix ".hidden.tar.gz").filePrefix? = some (Path.Filename.mk ".hidden".toByteArray)
#guard (posix ".hidden.lean").filePrefix? = some (Path.Filename.mk ".hidden".toByteArray)
-- no file name → none
#guard (posix "/").filePrefix? = none
#guard (posix "a/..").filePrefix? = none
#guard Path.empty.filePrefix? = none
-- consistency with fileStem?: filePrefix? drops all extensions, fileStem? only last
#guard (posix "a.b.c").filePrefix? = some (Path.Filename.mk "a".toByteArray)
#guard (posix "a.b.c").fileStem?    = some (Path.Filename.mk "a.b".toByteArray)

end FilePrefix


-- ---------------------------------------------------------------------------
-- Section: raw bytes
--
-- A component holds raw bytes, so a name that is not valid UTF-8 — which POSIX
-- permits — survives parsing and rendering untouched. Only the `String`-returning
-- half of the API decodes it, and that decoding is lossy.
-- ---------------------------------------------------------------------------

section RawBytes

-- "a\xffb": a lone 0xff begins no well-formed UTF-8 encoding.
private def illFormed : ByteArray := ⟨#[0x61, 0xff, 0x62]⟩
private def raw : Path := (Path.ofPosixBytes? ("/tmp/".toByteArray ++ illFormed)).get!

-- The bytes round-trip exactly.
#guard raw.toPosixBytes == "/tmp/".toByteArray ++ illFormed
#guard raw.filename?.map (·.value) == some illFormed
#guard raw.parent?.map (·.toPosixBytes) == some "/tmp".toByteArray

-- Rendering to a `String` replaces the ill-formed byte with U+FFFD.
#guard raw.toPosixString = "/tmp/a" ++ String.singleton (Char.ofNat 0xfffd) ++ "b"
#guard raw.filename?.map (·.toString) = some ("a" ++ String.singleton (Char.ofNat 0xfffd) ++ "b")

-- Globs match the decoded segment, so the ill-formed byte counts as one character.
#guard raw.matchGlob "**/a?b" = true

-- The string parsers are the byte parsers applied to the UTF-8 encoding.
#guard Path.ofPosixString? "/a/b" == Path.ofPosixBytes? "/a/b".toByteArray
#guard Path.ofWindowsString? "C:\\a" == Path.ofWindowsBytes? "C:\\a".toByteArray

-- Empty input and null bytes are rejected in byte form too.
#guard Path.ofPosixBytes? ByteArray.empty == none
#guard Path.ofWindowsBytes? ByteArray.empty == none
#guard Path.ofPosixBytes? ⟨#[0x61, 0x00, 0x62]⟩ == none
#guard Path.ofWindowsBytes? ⟨#[0x61, 0x00, 0x62]⟩ == none

-- A name that is not valid UTF-8 is still a valid `Filename` and `Extension`.
#guard (Path.Filename.ofBytes? illFormed).isSome
#guard (Path.Extension.ofBytes? illFormed).isSome
#guard Path.Filename.ofBytes? ByteArray.empty = none
#guard Path.Filename.ofBytes? "a/b".toByteArray = none

end RawBytes


-- ---------------------------------------------------------------------------
-- Section: WTF-8 and byte-level edges
--
-- The section above covers a POSIX name that is not valid UTF-8. This one covers
-- what is left: Windows bytes are WTF-8, which encodes an unpaired surrogate that
-- UTF-8 has no encoding for at all, and the byte-level order, `Repr`, and
-- rendering checks all have to hold up on names no `String` can carry.
-- ---------------------------------------------------------------------------

section Wtf8Edges

private def bs (s : String) : ByteArray := s.toByteArray
private def pb (b : ByteArray) : Path := (Path.ofPosixBytes? b).get!

-- `ED A0 80` encodes U+D800, an unpaired surrogate: a legal Windows path that no
-- UTF-8 decoder accepts and no `String` can hold.
private def surrogate : ByteArray := ⟨#[0xed, 0xa0, 0x80]⟩

-- A lone continuation byte followed by a byte that begins no encoding at all.
private def loose : ByteArray := ⟨#[0x80, 0xfe]⟩

-- A surrogate survives both parsers and both renderers untouched.
#guard (pb (bs "/" ++ surrogate ++ bs "/b")).toPosixBytes == bs "/" ++ surrogate ++ bs "/b"
#guard (Path.ofWindowsBytes? (bs "C:\\" ++ surrogate)).get!.toWindowsBytes == bs "C:\\" ++ surrogate

-- Decoding replaces one `U+FFFD` per byte that begins no well-formed encoding, so
-- the three bytes of a surrogate give three rather than one.
#guard (pb (bs "a/" ++ surrogate)).toPosixString.length == 5
#guard (pb (bs "a/" ++ loose)).toPosixString.length == 4

-- The name accessors past `filename?` hand the bytes back as parsed, not as decoded.
#guard (pb (bs "a/x." ++ surrogate)).extension?.map (·.value) == some surrogate
#guard ((pb (bs "a/" ++ loose ++ bs ".txt")).fileStem?.map Path.Filename.value) == some loose
#guard ((pb (bs "a/" ++ loose ++ bs ".txt")).filePrefix?.map Path.Filename.value) == some loose

-- `Filename` and `Extension` police separators and the null byte, not encoding.
#guard (Path.Filename.ofBytes? surrogate).isSome
#guard (Path.Filename.ofBytes? (bs "a" ++ ⟨#[0x5c]⟩)).isNone
#guard (Path.Filename.ofBytes? (loose ++ ⟨#[0x00]⟩)).isNone
#guard (Path.Extension.ofBytes? (surrogate ++ ⟨#[0x2e]⟩)).isNone

-- Bytes compare unsigned, so `0x80` sorts above `0x7f` rather than below it, and a
-- proper prefix still sorts ahead of what extends it.
#guard compare (Path.Segment.normal ⟨#[0x80]⟩) (Path.Segment.normal ⟨#[0x7f]⟩) == .gt
#guard compare (Path.Segment.normal ⟨#[0xff]⟩) (Path.Segment.normal ⟨#[0x01]⟩) == .gt
#guard compare (Path.Segment.normal loose) (Path.Segment.normal (loose ++ bs "a")) == .lt

-- `==`, `compare`, and `hash` agree on bytes no `String` can hold.
#guard (Path.Segment.normal surrogate) == (Path.Segment.normal surrogate)
#guard hash (Path.Segment.normal surrogate) == hash (Path.Segment.normal surrogate)
#guard !((Path.Segment.normal loose) == (Path.Segment.normal surrogate))
#guard (pb (bs "a/" ++ surrogate)) == (pb (bs "a/" ++ surrogate))

-- A glob matches each ill-formed byte as the single `U+FFFD` it would decode to, so
-- a surrogate takes three `?` and not one, and never matches an ASCII class.
#guard (pb (bs "a/" ++ surrogate)).matchGlob "a/???"
#guard !((pb (bs "a/" ++ surrogate)).matchGlob "a/?")
#guard (pb (bs "a/" ++ loose ++ bs ".lean")).matchGlob "a/*.lean"
#guard !((pb (bs "a/" ++ loose)).matchGlob "a/[a-z][a-z]")

-- A `Repr` that cannot spell the bytes as a string literal falls back to the byte
-- array, so what it prints still rebuilds the value.
#guard (repr (Path.Segment.normal loose)).pretty ==
  "Std.Path.Segment.normal (ByteArray.mk #[128, 254])"
#guard (repr ((Path.Filename.ofBytes? loose).get!)).pretty ==
  "Std.Path.Filename.mk (ByteArray.mk #[128, 254])"

-- A POSIX name may hold a `\`, which Windows syntax reads as a separator, so the
-- checked Windows render refuses it rather than silently splitting the name in two.
#guard (pb (bs "a/b\\c")).toPosixBytes?.isSome
#guard (pb (bs "a/b\\c")).toWindowsBytes?.isNone
#guard (pb (bs "a/b\\c")).toWindowsBytes == bs "a\\b\\c"

end Wtf8Edges


-- ---------------------------------------------------------------------------
-- Section: checked rendering (toPosixBytes? / toWindowsBytes? and the `String`
-- counterparts). The unchecked renderers are total and can name a different
-- path; these return `none` in exactly the cases `toBytes` refuses.
-- ---------------------------------------------------------------------------

section CheckedRender

-- A path anchored to nothing renders under either syntax.
#guard (posix "src/Main.lean").toPosixString? = some "src/Main.lean"
#guard (posix "src/Main.lean").toWindowsString? = some "src\\Main.lean"
#guard (win "src\\Main.lean").toPosixString? = some "src/Main.lean"
#guard (win "src\\Main.lean").toWindowsString? = some "src\\Main.lean"
#guard (posix "../x/./y").toWindowsString? = some "..\\x\\.\\y"
#guard (posix "a b/c d").toWindowsString? = some "a b\\c d"

-- Parsing `a\b` as POSIX and `a/b` as Windows gives the same value, so both render both ways.
#guard (posix "a/b") == (win "a\\b")
#guard (posix "a/b").toPosixBytes? == some "a/b".toByteArray
#guard (posix "a/b").toWindowsBytes? == some "a\\b".toByteArray

-- A Windows prefix has no POSIX spelling. Unchecked, each of these names somewhere else.
#guard (win "C:\\Users").toPosixString = "/Users"
#guard (win "C:\\Users").toPosixBytes? = none
#guard (win "C:foo\\bar").toPosixString = "foo/bar"
#guard (win "C:foo\\bar").toPosixBytes? = none
#guard (win "\\foo").toPosixString = "/foo"
#guard (win "\\foo").toPosixBytes? = none
-- A share or device path loses everything that named the host and renders as `.`.
#guard (win "\\\\server\\share").toPosixString = "."
#guard (win "\\\\server\\share").toPosixBytes? = none
#guard (win "\\\\server\\share\\a").toPosixString = "/a"
#guard (win "\\\\server\\share\\a").toPosixBytes? = none
#guard (win "\\\\?\\C:\\x").toPosixBytes? = none
#guard (win "\\\\.\\COM1").toPosixBytes? = none

-- A POSIX root is not a Windows root: `\a` names the root of whichever drive is current.
#guard (posix "/usr/lib").toWindowsString = "\\usr\\lib"
#guard (posix "/usr/lib").toWindowsBytes? = none

-- `\` is an ordinary byte in a POSIX name, and Windows syntax would split it in two.
#guard (posix "a\\b").segments.size = 1
#guard (posix "a\\b").toWindowsString = "a\\b"
#guard (posix "a\\b").toWindowsBytes? = none
#guard (posix "a\\b").toPosixBytes? = some "a\\b".toByteArray

-- A leading segment that reads back as a drive prefix is rejected, even though the path is
-- anchored to nothing and carries no separator of its own.
#guard (posix "C:a").segments.size = 1
#guard (posix "C:a").toWindowsString = "C:a"
#guard (posix "C:a").toWindowsBytes? = none
#guard (posix "C:/a").toWindowsBytes? = none
-- A `:` anywhere else is refused too, by `isWindowsPortable` rather than by the round-trip: this
-- parser reads `x\C:y` back as the name `C:y`, while Windows reads it as the `y` alternate data
-- stream of the file `x\C`.
#guard (posix "x/C:y").toWindowsBytes? = none

-- Checking is on the bytes, so an ill-formed name is judged before it is decoded.
#guard raw.toPosixBytes? == some ("/tmp/".toByteArray ++ illFormed)
#guard raw.toWindowsBytes? = none

-- A successful check returns exactly what the unchecked renderer produced.
#guard (posix "a/b/c").toPosixBytes? == some (posix "a/b/c").toPosixBytes
#guard (win "C:\\a").toWindowsBytes? == some (win "C:\\a").toWindowsBytes

-- `Path.empty` renders as `.`, which reads back as the one-segment `.` path rather than as
-- `Path.empty` itself. The check admits it anyway: the two name the same location, and it is what
-- a relative path that cancels to nothing normalizes to, so refusing it would leave the results of
-- `normalize`, `dropPrefix?`, and `relativeTo?` unrenderable.
#guard Path.empty.toPosixBytes? == some ".".toByteArray
#guard Path.empty.toWindowsBytes? == some ".".toByteArray
#guard (posix "a/..").normalize.toPosixString? = some "."
#guard (posix ".").normalize.toWindowsString? = some "."
#guard ((posix "/a/b").relativeTo? (posix "/a/b")).bind (·.toPosixString?) = some "."
#guard ((posix "a/b").dropPrefix? (posix "a/b")).bind (·.toPosixString?) = some "."
-- A Windows-prefixed path with no segments also renders as `.`, and that one is a genuine loss.
#guard (win "\\\\server\\share").toPosixBytes == ".".toByteArray
#guard (win "\\\\server\\share").toPosixBytes? = none

end CheckedRender

-- ---------------------------------------------------------------------------
-- Section: isWindowsPortable. Reading the render back is not enough on its own,
-- because Win32 normalizes a path further than this parser does: a name it
-- resolves to another name would pass the round-trip while naming something
-- else on the file system.
-- ---------------------------------------------------------------------------

section WindowsPortable

-- The seven printable bytes Windows keeps for itself, and the control bytes.
#guard !(posix "dir/b:c").isWindowsPortable
#guard !(posix "dir/a*b").isWindowsPortable
#guard !(posix "dir/a?b").isWindowsPortable
#guard !(posix "dir/a<b").isWindowsPortable
#guard !(posix "dir/a>b").isWindowsPortable
#guard !(posix "dir/a|b").isWindowsPortable
#guard !(posix "dir/a\"b").isWindowsPortable
#guard !(posix "dir/a\x01b").isWindowsPortable

-- Reserved device names, in any directory, in any case, and with any extension.
#guard !(posix "dir/CON").isWindowsPortable
#guard !(posix "dir/con").isWindowsPortable
#guard !(posix "dir/CON.txt").isWindowsPortable
#guard !(posix "dir/com1.tar.gz").isWindowsPortable
#guard !(posix "NUL/a").isWindowsPortable
#guard !(posix "dir/PRN").isWindowsPortable
#guard !(posix "dir/AUX").isWindowsPortable
#guard !(posix "dir/LPT9").isWindowsPortable
-- Near misses are ordinary names: the reservation is on the exact stem.
#guard (posix "dir/CONSOLE").isWindowsPortable
#guard (posix "dir/LPT10").isWindowsPortable
#guard (posix "dir/CO").isWindowsPortable
-- `COM0`/`LPT0` and the console devices are reserved too, and Win32 strips trailing spaces before
-- looking a name up, so a space does not get a name out of the reservation.
#guard !(posix "dir/COM0").isWindowsPortable
#guard !(posix "dir/LPT0").isWindowsPortable
#guard !(posix "dir/CONIN$").isWindowsPortable
#guard !(posix "dir/CONOUT$").isWindowsPortable
#guard !(posix "dir/CON .txt").isWindowsPortable

-- Win32 strips a trailing dot or space from a name, so one that has them names something else.
#guard !(posix "dir/foo.").isWindowsPortable
#guard !(posix "dir/foo ").isWindowsPortable
#guard !(posix "...").isWindowsPortable
#guard (posix "dir/.foo").isWindowsPortable
#guard (posix "dir/ foo").isWindowsPortable

-- `.` and `..` are segments rather than names, so the trailing-dot rule leaves them alone.
#guard (posix "a/./b").isWindowsPortable
#guard (posix "a/../b").isWindowsPortable

-- A verbatim path is handed to the file system as written, so every one of these is reachable.
#guard (win "\\\\?\\C:\\NUL").isWindowsPortable
#guard (win "\\\\?\\C:\\foo.").isWindowsPortable

-- The checked Windows renderers refuse what this rejects; POSIX rendering is untouched.
#guard (posix "dir/NUL").toWindowsBytes? = none
#guard (posix "dir/NUL").toWindowsString? = none
#guard (posix "dir/NUL").toWindowsString = "dir\\NUL"
#guard (posix "dir/NUL").toPosixString? = some "dir/NUL"
#guard (posix "dir/b:c").toPosixString? = some "dir/b:c"
#guard (win "\\\\?\\C:\\NUL").toWindowsString? = some "\\\\?\\C:\\NUL"

end WindowsPortable

-- ---------------------------------------------------------------------------
-- Section: joinRelative? / isNormalized
-- ---------------------------------------------------------------------------

section LexicalGuards

-- `join` lets an anchored right-hand side replace the base; `joinRelative?` refuses one.
#guard ((posix "/srv/up") / (posix "/etc/passwd")).toPosixString = "/etc/passwd"
#guard ((posix "/srv/up").joinRelative? (posix "a/b")).map (·.toPosixString) = some "/srv/up/a/b"
#guard (posix "/srv/up").joinRelative? (posix "/etc/passwd") = none
#guard (posix "/srv/up").joinRelative? (win "\\foo") = none
#guard (posix "/srv/up").joinRelative? (win "C:foo") = none
#guard (posix "/srv/up").joinRelative? (win "C:\\foo") = none
-- It is a check on the anchor alone: a `..` still walks out, which is `isUnder`'s question.
#guard ((posix "/srv/up").joinRelative? (posix "../etc")).map (·.toPosixString) = some "/srv/up/../etc"
#guard !((posix "/srv/up").joinRelative? (posix "../etc")).get!.isUnder (posix "/srv/up")

-- `isNormalized` asks about the spelling, so it reads segments rather than components.
#guard (posix "a/b").isNormalized
#guard (posix "../a").isNormalized
#guard (win "C:..\\a").isNormalized
#guard !(posix "a/./b").isNormalized
#guard (posix "a/./b") == (posix "a/b")
#guard !(posix "a/../b").isNormalized
#guard !(posix "/../a").isNormalized
#guard Path.empty.isNormalized
-- `normalize` is idempotent, so its result always passes.
#guard (posix "/a/./b/../c").normalize.isNormalized
-- A verbatim path is left alone by `normalize`, so it always passes too.
#guard (win "\\\\?\\C:\\a\\..\\b").isNormalized

end LexicalGuards

-- ---------------------------------------------------------------------------
-- Section: Filename name surgery (the same operations `Path` applies to a last
-- component, applied to a name standing on its own)
-- ---------------------------------------------------------------------------

section FilenameSurgery

open Path (Filename Extension)

private def fn (s : String) : Filename := Filename.ofString! s
private def ext (s : String) : Extension := Extension.ofString! s

#guard (fn "archive.tar.gz").stem? == some (fn "archive.tar")
#guard (fn "Main.lean").stem? == some (fn "Main")
#guard (fn "Makefile").stem? == some (fn "Makefile")
#guard (fn ".gitignore").stem? == some (fn ".gitignore")
-- Truncation that would leave `.` or `..` has no `Filename` to return.
#guard (fn "..a").stem? == none

#guard (fn "foo.tar.gz").prefix? == some (fn "foo")
#guard (fn ".hidden.tar.gz").prefix? == some (fn ".hidden")
#guard (fn ".hidden").prefix? == some (fn ".hidden")

#guard (fn "Main.lean").extension? == some (ext "lean")
#guard (fn "archive.tar.gz").extension? == some (ext "gz")
#guard (fn "Makefile").extension? == none
#guard (fn ".gitignore").extension? == none
#guard (fn "a.").extension? == none
#guard (fn "Main.lean").hasExtension
#guard !(fn "Makefile").hasExtension

#guard (fn "archive.tar.gz").suffixes == #[ext "tar", ext "gz"]
#guard (fn "Makefile").suffixes == #[]
#guard (fn "a..b").suffixes == #[ext "b"]
#guard (fn "a.b.").suffixes == #[ext "b"]

#guard (fn "archive.tar.gz").withExtension (ext "xz") == fn "archive.tar.xz"
#guard (fn "Makefile").withExtension (ext "txt") == fn "Makefile.txt"
#guard (fn "archive.tar").addExtension (ext "gz") == fn "archive.tar.gz"
#guard (fn "archive.tar.gz").removeExtension == fn "archive.tar"
#guard (fn "a.").removeExtension == fn "a"
-- A name whose extension cannot be removed without leaving `.` or `..` keeps it.
#guard (fn "..a").removeExtension == fn "..a"
#guard (fn "...").removeExtension == fn "..."
#guard (fn "Makefile").removeExtension == fn "Makefile"

#guard (fn "archive.tar.gz").withStem (fn "backup") == fn "backup.gz"
#guard (fn "archive.tar.gz").withPrefix (fn "backup") == fn "backup.tar.gz"
#guard ((fn "archive.tar.gz").withPrefix (fn "backup")).suffixes == (fn "archive.tar.gz").suffixes
#guard (fn "Makefile").withStem (fn "GNUmakefile") == fn "GNUmakefile"

#guard (fn ".gitignore").isHidden
#guard !(fn "gitignore").isHidden

-- The `Path` operations agree with them on the last component.
#guard (posix "a/archive.tar.gz").fileStem? == (fn "archive.tar.gz").stem?
#guard (posix "a/archive.tar.gz").filePrefix? == (fn "archive.tar.gz").prefix?
#guard (posix "a/archive.tar.gz").extension? == (fn "archive.tar.gz").extension?
#guard (posix "a/archive.tar.gz").suffixes == (fn "archive.tar.gz").suffixes
#guard ((posix "a/archive.tar.gz").withExtension (ext "xz")).filename?
        == some ((fn "archive.tar.gz").withExtension (ext "xz"))
#guard (posix "a/archive.tar.gz").removeExtension.filename?
        == some ((fn "archive.tar.gz").removeExtension)

end FilenameSurgery

-- ---------------------------------------------------------------------------
-- Section: ofSegments? / withSegments?, the way back in for a caller that took
-- a path apart with `components`
-- ---------------------------------------------------------------------------

section Reassembly

#guard (Path.ofSegments? #[.normal "a".toByteArray, .normal "b".toByteArray]).map (·.toPosixString)
        = some "a/b"
#guard (Path.ofSegments? #[.current, .normal "a".toByteArray]).map (·.toPosixString) = some "./a"
#guard (Path.ofSegments? #[.parent]).map (·.toPosixString) = some ".."
#guard (Path.ofSegments? #[]).map (·.toPosixString) = some "."

-- Everything the parsers refuse is refused here too, which is what keeps the segments of a `Path`
-- free of anything its syntax gives meaning to.
#guard Path.ofSegments? #[.normal "a/b".toByteArray] = none
#guard Path.ofSegments? #[.normal ByteArray.empty] = none
#guard Path.ofSegments? #[.normal ⟨#[0x61, 0x00]⟩] = none
-- A name spelled like a special segment would render as one and read back as a different path.
#guard Path.ofSegments? #[.normal ".".toByteArray] = none
#guard Path.ofSegments? #[.normal "..".toByteArray] = none

-- The anchor comes from the path, so what counts as a name depends on its flavour. An unanchored
-- path is checked against POSIX syntax, where `\` is an ordinary byte; the Windows renderer is what
-- refuses such a name later.
#guard (Path.ofSegments? #[.normal "a\\b".toByteArray]).map (·.toPosixString) = some "a\\b"
#guard (Path.ofSegments? #[.normal "a\\b".toByteArray]).bind (·.toWindowsBytes?) = none

#guard ((posix "/usr/local").withSegments? #[.normal "opt".toByteArray]).map (·.toPosixString)
        = some "/opt"
#guard ((win "C:\\x").withSegments? #[.normal "a".toByteArray]).map (·.toWindowsString)
        = some "C:\\a"
#guard (win "C:\\x").withSegments? #[.normal "a/b".toByteArray] = none
-- Only a verbatim path can hold a `/` in a name, and only it rejects `.` and `..`, which it would
-- read back as ordinary names rather than as the special segments.
#guard ((win "\\\\?\\C:\\x").withSegments? #[.normal "a/b".toByteArray]).map (·.toWindowsString)
        = some "\\\\?\\C:\\a/b"
#guard (win "\\\\?\\C:\\x").withSegments? #[.current] = none

-- The round trip that motivates it: take a path apart, drop a component, put it back together.
#guard (let p := posix "/a/./b/c"
        (p.withSegments? (p.components.filter (· != .normal "b".toByteArray))).map (·.toPosixString))
        = some "/a/c"
#guard (let p := posix "/a/b"; (p.withSegments? p.segments) == some p)

end Reassembly

-- ---------------------------------------------------------------------------
-- Section: IO boundary (pathSeparator / ofBytes / toBytes / ofString /
-- toString / currentDir / cwd / resolve). These exercise the platform-native
-- rendering path and the `lean_uv_cwd` and `lean_uv_realpath` FFI bindings.
-- Assertions are written to hold on both POSIX and Windows hosts.
-- ---------------------------------------------------------------------------

section IOOps

-- `pathSeparators` always contains the primary `pathSeparator`.
#eval do
  let sep ← Path.pathSeparator
  let seps ← Path.pathSeparators
  unless seps.contains sep do
    throw (IO.userError "pathSeparators must contain pathSeparator")

-- `ofString` / `toString` round-trip a path built from the native separator.
#eval do
  let sep ← Path.pathSeparator
  let raw := s!"{sep}usr{sep}local{sep}bin"
  let rendered ← (← Path.ofString raw).toString
  unless rendered == raw do
    throw (IO.userError s!"ofString/toString round-trip failed: {rendered}")

-- `toBytes` is the host's checked renderer: it succeeds on exactly the paths whose
-- `toPosixBytes?` / `toWindowsBytes?` succeeds, and returns the same bytes.
#eval show IO Unit from do
  let cases : Array Path := #[posix "a/b", posix "/usr/lib", posix "a\\b", posix "C:a",
    win "C:\\Users", win "\\foo", win "\\\\server\\share", win "src\\Main.lean"]
  for p in cases do
    let expected := if System.Platform.isWindows then p.toWindowsBytes? else p.toPosixBytes?
    let actual := (← p.toBytes.toBaseIO).toOption
    unless actual == expected do
      throw (IO.userError s!"toBytes disagrees with the pure check on {p.toPosixString}")

-- `cwd` turns a relative path into an absolute one, keeping the tail.
#eval do
  let abs ← Path.cwd (posix "a/b")
  unless abs.isAbsolute do
    throw (IO.userError "cwd should produce an absolute path")
  unless abs.endsWith (posix "a/b") do
    throw (IO.userError s!"cwd dropped the relative tail: {← abs.toString}")

-- `cwd` is a no-op on an already-absolute path.
#eval do
  let p := posix "/usr/local"
  unless (← Path.cwd p) == p do
    throw (IO.userError "cwd should leave absolute paths unchanged")

-- `resolve` of an existing path yields an absolute, canonical path.
#eval do
  let abs ← Path.resolve (posix ".")
  unless abs.isAbsolute do
    throw (IO.userError s!"resolve '.' should be absolute: {← abs.toString}")

-- `resolve` of a nonexistent path fails (realpath errors on a missing component).
#eval (do
  match ← (Path.resolve (posix "/no/such/path/for/std-path-test")).toBaseIO with
  | .ok _ => throw (IO.userError "resolve should have failed on a nonexistent path")
  | .error _ => pure () : IO Unit)

-- `ofBytes` / `toBytes` round-trip a path that no `String` can hold.
#eval do
  let sep ← Path.pathSeparator
  let rawBytes := s!"usr{sep}".toByteArray ++ illFormed
  let p ← Path.ofBytes rawBytes
  unless (← p.toBytes) == rawBytes do
    throw (IO.userError "ofBytes/toBytes round-trip lost bytes")

-- `toString` is the lossy view of the same path.
#eval do
  let sep ← Path.pathSeparator
  let p ← Path.ofBytes (s!"usr{sep}".toByteArray ++ illFormed)
  unless (← p.toString) == s!"usr{sep}a" ++ String.singleton (Char.ofNat 0xfffd) ++ "b" do
    throw (IO.userError s!"toString should replace the ill-formed byte: {← p.toString}")

-- `currentDir` reads the working directory itself.
#eval do
  unless (← Path.currentDir).isAbsolute do
    throw (IO.userError "currentDir should be absolute")

-- `setCurrentDir` moves the process, and `currentDir` reads back the directory it named. The
-- original directory is restored so the rest of the file still resolves relative paths against it.
#eval do
  let original ← Path.currentDir
  let target ← (← Path.tempDir).resolve
  try
    Path.setCurrentDir target
    unless (← (← Path.currentDir).resolve) == target do
      throw (IO.userError s!"setCurrentDir did not move to {← target.toString}")
  finally
    Path.setCurrentDir original
  unless (← Path.currentDir) == original do
    throw (IO.userError "setCurrentDir did not restore the original working directory")

-- So do `homeDir` and `tempDir`, and both come back as bytes, so they survive a `toBytes` that
-- checks the render reads back as the same path.
#eval do
  let home ← Path.homeDir
  unless home.isAbsolute do
    throw (IO.userError s!"homeDir should be absolute: {← home.toString}")
  let _ ← home.toBytes
  let tmp ← Path.tempDir
  unless tmp.isAbsolute do
    throw (IO.userError s!"tempDir should be absolute: {← tmp.toString}")
  unless (← System.FilePath.isDir (← tmp.toString)) do
    throw (IO.userError "tempDir should name a directory")

-- `exeExtension` is the extension an executable carries here, and `none` where it carries none.
#eval do
  let ext ← Path.exeExtension
  unless ext.map Path.Extension.value ==
      (if System.Platform.isWindows then some "exe".toByteArray else none) do
    throw (IO.userError "exeExtension disagrees with the host platform")
  let p := Path.ofPosixString! "bin/lean"
  let exe := match ext with | some e => p.addExtension e | none => p
  unless exe.toPosixString == (if System.Platform.isWindows then "bin/lean.exe" else "bin/lean") do
    throw (IO.userError s!"exeExtension did not name the host's executable: {exe.toPosixString}")

-- A search path splits and rejoins on the host's separator, keeping its entries in order.
#eval do
  let sep ← Path.searchPathSeparator
  let sp : Path.SearchPath ← Path.SearchPath.ofString s!"/usr/bin{sep}/usr/local/bin"
  unless sp.map Path.toPosixString == ["/usr/bin", "/usr/local/bin"] do
    throw (IO.userError "SearchPath.ofString split the entries wrongly")
  unless (← Path.SearchPath.toString sp) == s!"/usr/bin{sep}/usr/local/bin" do
    throw (IO.userError "SearchPath.toString did not rejoin on the host separator")

-- POSIX gives a zero-length entry the meaning "the working directory", which is what `Path.empty`
-- renders as, so the entry is kept rather than dropped.
#eval do
  let sep ← Path.searchPathSeparator
  let sp : Path.SearchPath ← Path.SearchPath.ofString s!"a{sep}{sep}b"
  unless sp.map Path.toPosixString == ["a", ".", "b"] do
    throw (IO.userError "an empty search-path entry should become `.`")

-- Entries that are not valid UTF-8 survive, which is why the byte form is the primitive one.
#eval do
  let sepByte : UInt8 := if System.Platform.isWindows then 0x3b else 0x3a
  let raw := "a".toByteArray ++ (ByteArray.mk #[sepByte]) ++ (ByteArray.mk #[0xff])
  let sp ← Path.SearchPath.ofBytes raw
  unless (← Path.SearchPath.toBytes sp) == raw do
    throw (IO.userError "SearchPath lost bytes on the round trip")

-- `resolve` hands the file name back byte for byte, over the FFI and through a name that needs
-- more than one byte per character.
#eval show IO Unit from IO.FS.withTempDir fun dir => do
  let name := Path.Filename.ofString! "caf\u00e9-\u65e5\u672c.txt"
  let dirPath ← Path.ofString dir.toString
  let file := dirPath / name
  IO.FS.writeFile (← file.toString) ""
  let resolved ← Path.resolve file
  unless resolved.filename?.map (·.value) == some name.value do
    throw (IO.userError s!"resolve mangled a non-ASCII file name: {← resolved.toString}")

-- The same, for a name that is not valid UTF-8 at all. Only a file system that accepts such a name
-- can run the check (Linux does, APFS and NTFS do not), so a name the shell failed to create is
-- skipped; once it exists, `resolve` must reproduce it exactly.
#eval show IO Unit from IO.FS.withTempDir fun dir => do
  let created ← (IO.Process.run
    { cmd := "sh", args := #["-c", s!"cd '{dir}' && touch \"$(printf 'a\\377b')\""] }).toBaseIO
  if created.isOk then
    let dirPath ← Path.ofString dir.toString
    let bad := dirPath / (Path.Filename.ofBytes? illFormed).get!
    let resolved ← Path.resolve bad
    unless resolved.filename?.map (·.value) == some illFormed do
      throw (IO.userError s!"resolve mangled a non-UTF-8 file name: {← resolved.toString}")

-- `resolveWithin` must judge a path by where it actually leads, not by how it is spelled: a
-- symbolic link out of the tree escapes, and a `..` behind one is not the identity `normalize`
-- would make it. `isUnder` is the lexical test and cannot see either.
#eval show IO Unit from IO.FS.withTempDir fun dir => do
  let base := (← Path.ofString dir.toString) / Path.Filename.mk "jail".toByteArray
  let inside := base / Path.Filename.mk "sub".toByteArray
  IO.FS.createDirAll (← inside.toString)
  IO.FS.createDirAll (← ((← Path.ofString dir.toString) / Path.Filename.mk "outside".toByteArray).toString)
  IO.FS.writeFile (← (inside / Path.Filename.mk "ok.txt".toByteArray).toString) ""
  let _ ← IO.Process.run
    { cmd := "sh", args := #["-c", s!"cd '{dir}/jail' && ln -s ../outside escape && ln -s sub in \
       && ln -s ../outside/gone dangling && ln -s sub/gone inner \
       && ln -s dangling tolink"] }

  let ok (rel : String) : IO Unit := do
    discard <| base.resolveWithin (posix rel)
  let rejects (rel : String) : IO Unit := do
    if (← (base.resolveWithin (posix rel)).toBaseIO).isOk then
      throw (IO.userError s!"resolveWithin admitted a path it cannot vouch for: {rel}")

  ok "sub/ok.txt"
  -- a path that does not exist yet is still resolvable, so a file can be created through the check
  ok "sub/new.txt"
  ok "new/deep/nested.txt"
  ok "in/ok.txt"
  ok "sub/../sub/ok.txt"
  rejects "../outside"
  rejects "escape/x"
  -- the `..` here cancels the link only lexically; on the file system it lands outside
  rejects "escape/../../outside/x"
  -- an absolute path would replace the base under `join` rather than extend it
  rejects "/etc/passwd"

  -- A symbolic link whose target does not exist is `noFileOrDirectory` to `resolve`, exactly as a
  -- name that is not there at all is. Taking it for the latter and appending it as written would
  -- return a path inside the jail that the OS still follows out of it, so it is refused.
  rejects "dangling"
  rejects "dangling/x"
  -- refused whichever way the link points, since `resolve` cannot see where that is
  rejects "inner"
  -- a link pointing at a dangling link is caught at the first `isSymlink`, with no chasing: this is
  -- the case that reading the link and resolving it by hand would have needed loop detection for
  rejects "tolink"

  -- `isSymlink` is what separates the two, and it is what `resolveWithin` rests on.
  unless ← (base / Path.Filename.mk "dangling".toByteArray).isSymlink do
    throw (IO.userError "isSymlink should see a link whose target is missing")
  unless ← (base / Path.Filename.mk "escape".toByteArray).isSymlink do
    throw (IO.userError "isSymlink should see a link whose target exists")
  if ← (base / posix "sub/ok.txt").isSymlink then
    throw (IO.userError "isSymlink should be false for an ordinary file")
  if ← (base / Path.Filename.mk "gone".toByteArray).isSymlink then
    throw (IO.userError "isSymlink should be false for a name that is not there")

  -- `isUnder` is blind to the link, which is why `resolveWithin` exists
  unless (base / posix "escape/x").isUnder base do
    throw (IO.userError "isUnder should accept the lexically-contained path")

end IOOps


-- ---------------------------------------------------------------------------
-- Section: Ord, LT/LE
-- ---------------------------------------------------------------------------

section Ordering

-- Segments sort by kind, so the two special names come ahead of every ordinary one.
#guard compare Path.Segment.current Path.Segment.parent = .lt
#guard compare Path.Segment.parent (Path.Segment.normal "a".toByteArray) = .lt
#guard compare (Path.Segment.normal "a".toByteArray) (Path.Segment.normal "b".toByteArray) = .lt
-- a proper prefix sorts ahead of what extends it
#guard compare (Path.Segment.normal "a".toByteArray) (Path.Segment.normal "ab".toByteArray) = .lt
-- the ordinary names only a verbatim path produces stay distinct from the special segments
#guard compare Path.Segment.parent (Path.Segment.normal "..".toByteArray) = .lt

-- Anchors sort by kind, and two Windows anchors by prefix and then by root.
#guard compare Path.Anchor.neutral Path.Anchor.posix = .lt
#guard compare Path.Anchor.posix (Path.Anchor.ofWindows none true) = .lt
#guard compare (Path.Anchor.ofWindows (some "C:".toByteArray) false)
               (Path.Anchor.ofWindows (some "C:".toByteArray) true) = .lt
#guard compare (Path.Anchor.ofWindows (some "C:".toByteArray) true)
               (Path.Anchor.ofWindows (some "D:".toByteArray) true) = .lt

-- Paths sort by anchor first, then segment by segment.
#guard compare (posix "a") (posix "/a") = .lt
#guard compare (posix "a/b") (posix "a/c") = .lt
#guard compare (posix "a") (posix "a/b") = .lt
#guard compare (posix "a/b") (posix "a/b") = .eq
#guard compare Path.empty (posix "a") = .lt

-- `compare` folds drive-letter case exactly as `==` does, so the two agree where `=` does not.
#guard (win "c:/a") == (win "C:/a")
#guard compare (win "c:/a") (win "C:/a") = .eq
#guard compare (win "c:/a") (win "C:/b") = .lt
#guard !(decide ((win "c:/a") = (win "C:/a")))

-- `<` and `≤` follow `compare`, and both are decidable.
#guard posix "a" < posix "b"
#guard posix "a" ≤ posix "a"
#guard !(posix "b" < posix "a")
#guard !(posix "b" ≤ posix "a")

-- Sorting a set of paths is what the order is for.
#guard ((#[posix "b", posix "/a", posix "a/b", posix "a"].qsort (· < ·)).map (·.toPosixString))
  = #["a", "a/b", "b", "/a"]

-- File names and extensions order by their bytes.
#guard compare (Path.Filename.ofString! "a") (Path.Filename.ofString! "b") = .lt
#guard Path.Filename.ofString! "a" < Path.Filename.ofString! "ab"
#guard compare (Path.Extension.ofString! "gz") (Path.Extension.ofString! "tar") = .lt

end Ordering


-- ---------------------------------------------------------------------------
-- Section: Repr
-- ---------------------------------------------------------------------------

section Reprs

-- A path reprs as the call that rebuilds it, in the syntax of the flavour it was parsed with.
/-- info: Std.Path.ofPosixString! "/usr/bin" -/
#guard_msgs in #eval posix "/usr/bin"

/-- info: Std.Path.ofWindowsString! "C:\\Users" -/
#guard_msgs in #eval win "C:\\Users"

/-- info: Std.Path.ofWindowsString! "\\\\server\\share\\a" -/
#guard_msgs in #eval win "\\\\server\\share\\a"

-- Nothing is normalized away first, so the repr reproduces the path as written.
/-- info: Std.Path.ofPosixString! "a/./../b" -/
#guard_msgs in #eval posix "a/./../b"

-- `Path.empty` renders as `.`, which reads back as a different path, so it reprs as itself.
/-- info: Std.Path.empty -/
#guard_msgs in #eval Path.empty

/-- info: Std.Path.ofPosixString! "." -/
#guard_msgs in #eval posix "."

-- A path whose render would not read back falls back to the anchor and segments. Here the `/` is an
-- ordinary byte in a name the verbatim parser produced, and no POSIX rendering can say so. Only
-- `ofParts` builds such a path: `relativeTo?` and `dropPrefix?` refuse to re-anchor a name that
-- would be read as structure once the verbatim anchor is gone.
/--
info: Std.Path.ofParts Std.Path.Anchor.neutral #[Std.Path.Segment.parent, Std.Path.Segment.normal "a/b".toByteArray]
-/
#guard_msgs in
#eval Path.ofParts .neutral #[.parent, .normal "a/b".toByteArray]

#guard (Path.relativeTo? (win "\\\\?\\C:\\x") (win "\\\\?\\C:\\a/b")) == none

-- So does a path whose bytes no string literal can hold.
/-- info: Std.Path.ofParts Std.Path.Anchor.posix #[Std.Path.Segment.normal (ByteArray.mk #[255, 254])] -/
#guard_msgs in
#eval (Path.ofPosixBytes? ("/".toByteArray ++ ⟨#[0xff, 0xfe]⟩)).get!

-- The components repr as the terms that rebuild them.
/-- info: Std.Path.Filename.ofString! "Main.lean" -/
#guard_msgs in #eval Path.Filename.ofString! "Main.lean"

/-- info: Std.Path.Extension.ofString! "lean" -/
#guard_msgs in #eval Path.Extension.ofString! "lean"

/-- info: Std.Path.Segment.current -/
#guard_msgs in #eval Path.Segment.current

/-- info: Std.Path.Segment.normal "src".toByteArray -/
#guard_msgs in #eval Path.Segment.normal "src".toByteArray

/-- info: Std.Path.Anchor.posix -/
#guard_msgs in #eval Path.Anchor.posix

-- A Windows prefix is shown in the case it was written in, which is what rendering writes back.
/-- info: Std.Path.Anchor.windows (some "c:".toByteArray) true -/
#guard_msgs in #eval (win "c:/a").anchor

end Reprs

-- ---------------------------------------------------------------------------
-- Section: parser edge cases
-- ---------------------------------------------------------------------------

section ParserEdges

-- `UNC` only introduces a share when a server segment follows it; on its own it is the volume name.
#guard (win "\\\\?\\UNC").windowsPrefix? == some "\\\\?\\UNC".toByteArray
#guard (win "\\\\?\\UNC\\").windowsPrefix? == some "\\\\?\\UNC".toByteArray
#guard (win "\\\\?\\UNC\\").toWindowsString = "\\\\?\\UNC\\"
#guard (win "\\\\?\\UNC\\s").windowsPrefix? == some "\\\\?\\UNC\\s".toByteArray
#guard (win "\\\\?\\UNC\\srv\\shr").windowsPrefix? == some "\\\\?\\UNC\\srv\\shr".toByteArray

-- Separator runs inside a prefix are written back as a single separator.
#guard (win "\\\\?\\UNC\\\\srv\\\\\\shr\\x").windowsPrefix? == some "\\\\?\\UNC\\srv\\shr".toByteArray
#guard (win "\\\\?\\UNC\\\\srv\\\\\\shr\\x").segments.map toString = #["x"]
#guard (win "\\\\srv\\\\\\shr\\\\x").windowsPrefix? == some "\\\\srv\\shr".toByteArray
#guard (win "\\\\srv\\\\\\shr\\\\x").segments.map toString = #["x"]

-- A UNC prefix with a server but no share keeps the root that follows it.
#guard (win "\\\\server\\").windowsPrefix? == some "\\\\server".toByteArray
#guard (win "\\\\server\\").toWindowsString = "\\\\server\\"
#guard (win "\\\\.\\").windowsPrefix? == some "\\\\.".toByteArray

-- Only the literal `\\?\` spelling is verbatim: `\\?x` is an ordinary server name, and `//?/x` is
-- refused as one, so it parses as a rooted path with `?` as its first segment.
#guard (win "\\\\?x").windowsPrefix? == some "\\\\?x".toByteArray
#guard (win "//?/x").windowsPrefix? == none
#guard (win "//?/x").segments.map toString = #["?", "x"]

-- A third separator is not part of the prefix, since the server segment must be non-empty.
#guard (win "\\\\\\a").windowsPrefix? == none
#guard (win "\\\\\\a").segments.map toString = #["a"]

-- A bare drive letter leaves the path relative, with or without a segment behind it.
#guard (win "C:").windowsPrefix? == some "C:".toByteArray
#guard (win "C:").isRelative
#guard (win "C:a").toWindowsString = "C:a"

end ParserEdges

-- ---------------------------------------------------------------------------
-- Section: `toPosixBytes?` agrees with its round-trip specification
-- ---------------------------------------------------------------------------

section PosixRenderSpec

/--
What `toPosixBytes?` promises: the render, provided POSIX syntax reads it back as the same path.
`toPosixBytes?` decides this from the structure of the path instead, so the two must agree.
-/
private def posixRenderSpec (p : Path) : Option ByteArray :=
  if Path.ofPosixBytes? p.toPosixBytes == some p then some p.toPosixBytes else none

private def parsedCases : Array Path :=
  (#["/", ".", "..", "a", "/a", "a/b", "/a/b/c", "a/./b", "a/../b", "/../a", "./.", "a/b/",
     "///a//b", "/.", "a/..", "a\\b", ".hidden/x"]).map posix ++
  (#["\\\\", "C:", "C:\\", "C:a", "\\a", "\\\\server\\share", "\\\\server\\share\\a", "\\\\.\\COM42",
     "\\\\?\\C:\\a", "\\\\?\\a/b", "\\\\?\\a\\.\\b", "\\\\?\\a\\..\\b", "\\\\?\\UNC\\s\\h\\x",
     "a\\b", "//?/x"]).map win

-- Segments that no parse produces but that `dropPrefix?` and `relativeTo?` can carry out of a
-- verbatim path, alongside the ones every parse does.
private def adversarialCases : Array Path := Id.run do
  let anchors : Array Path.Anchor :=
    #[.neutral, .posix, .windows none true, .windows (some "C:".toByteArray) false,
      .windows (some "C:".toByteArray) true, .windows (some "\\\\s\\h".toByteArray) true,
      .windows (some "\\\\?\\C:".toByteArray) true]
  let segs : Array Path.Segment :=
    #[.current, .parent, .normal "a".toByteArray, .normal ".".toByteArray,
      .normal "..".toByteArray, .normal "".toByteArray, .normal "a/b".toByteArray,
      .normal "a\\b".toByteArray, .normal ⟨#[0]⟩, .normal "C:".toByteArray]
  let mut out := #[]
  for a in anchors do
    out := out.push (Path.ofParts a #[])
    for s in segs do
      out := out.push (Path.ofParts a #[s])
      out := out.push (Path.ofParts a #[.normal "x".toByteArray, s])
      out := out.push (Path.ofParts a #[s, .normal "x".toByteArray])
  return out

#guard (parsedCases ++ adversarialCases).all fun p => p.toPosixBytes? == posixRenderSpec p

end PosixRenderSpec

/-!
## Regressions from the adversarial review

Each block below pins a bug the review found. The comment says what the wrong answer was, since
that is what a future change is at risk of reintroducing.
-/

section AdversarialRegressions

/-!
`isUnder` read a base with no components as matching everything, because `isPrefixOf` is vacuously
true there and `normalize` keeps a leading `..` under an unrooted anchor. `.` and `Path.empty` are
the likeliest sandbox roots of all, so every `..` escape was reported as contained.
-/
#guard !(posix "../../etc/passwd").isUnder (posix ".")
#guard !(posix "../../etc/passwd").isUnder Path.empty
#guard !(posix "../../../root/.ssh").isUnder (posix "uploads/..")
#guard !(posix "../../etc").isUnder (posix "..")
#guard !(posix "..").isUnder (posix ".")
-- ...while everything that really is contained still is.
#guard (posix "../a").isUnder (posix "..")
#guard (posix "a/b").isUnder (posix ".")
#guard (posix "a/b").isUnder Path.empty
#guard (posix ".").isUnder (posix ".")
#guard (posix "/srv/a").isUnder (posix "/srv")

/-!
`relativeTo?` and `dropPrefix?` re-anchored the components of a verbatim path onto a neutral one
without rechecking them. A verbatim `..` is an ordinary name, so the result was a relative path
holding `..` segments that `normalize` could not see and `isNormalized` called normalized.
-/
#guard (Path.relativeTo? (win "\\\\?\\C:\\up") (win "\\\\?\\C:\\up\\..\\..\\etc")) == none
#guard ((win "\\\\?\\C:\\up\\x/y").dropPrefix? (win "\\\\?\\C:\\up")) == none
#guard ((win "\\\\?\\C:\\up\\..").dropPrefix? (win "\\\\?\\C:\\up")) == none
-- An ordinary name still moves across.
#guard ((win "\\\\?\\C:\\up\\a").dropPrefix? (win "\\\\?\\C:\\up")).map Path.toPosixString == some "a"
#guard ((posix "/a/b/c").dropPrefix? (posix "/a")).map Path.toPosixString == some "b/c"

/-!
Joining a rootless Windows path onto a POSIX one read `windowsPrefix?`, which is `none` there, and
so dropped the POSIX root: the result was a drive-relative Windows path whose `isAbsolute` was
`false` even though the input's was `true`.
-/
#guard ((posix "/srv/uploads").join (win "\\foo")).isAbsolute
#guard ((posix "/srv/uploads").join (win "\\foo")).toPosixString? == some "/foo"
#guard ((posix "/srv/uploads").join (win "\\foo")).anchor == .posix

/-!
`toPosixString?` checked the render but not the decode, so a path whose bytes are not valid UTF-8
came back with `U+FFFD` standing in for them — a `some` naming a different file, and a collision
between every path that differs only in undecodable bytes.
-/
#guard (Path.ofPosixBytes? ("/tmp/a".toByteArray ++ ⟨#[0xC0, 0xAF]⟩)).bind (·.toPosixString?) == none
#guard ((Path.ofPosixBytes? ("/tmp/a".toByteArray ++ ⟨#[0xC0, 0xAF]⟩)).bind (·.toPosixBytes?)).isSome
#guard (posix "/a/b").toPosixString? == some "/a/b"

/-!
`withExtension` split on the last `.` while `hasExtension` reported the empty extension as no
extension, so a name ending in `.` was truncated where the docstring promised an append: guarding
with `if !hasExtension` renamed `backup.` to `backup.gz` instead of `backup..gz`.
-/
#guard ((Path.Filename.ofString! "backup.").withExtension (.mk "gz".toByteArray)).toString ==
  "backup..gz"
#guard ((Path.Filename.ofString! "a.tar.gz").withExtension (.mk "xz".toByteArray)).toString ==
  "a.tar.xz"
#guard ((posix "d/backup.").withExtension (.mk "gz".toByteArray)).toPosixString == "d/backup..gz"

/-!
`[^...]` parsed as a positive class holding `^`, so a pattern written to exclude dotfiles matched
only dotfiles — a deny-list inverted with no parse error.
-/
#guard !(posix ".ssh").matchGlob "[^.]*"
#guard !(posix ".ssh").matchGlob "[!.]*"
#guard (posix "ssh").matchGlob "[^.]*"
#guard (posix "b").matchGlob "[abc]"
#guard (posix "^").matchGlob "[]^]"

end AdversarialRegressions

/-!
`SearchPath.toBytes` rendered each entry but never checked it for the separator, so one directory
going in came back out as two — and an entry ending in the separator added an empty one, which is
the working directory. The separator is an ordinary name byte on POSIX.
-/
#eval show IO Unit from do
  let sep := if System.Platform.isWindows then ";" else ":"
  let evil ← Path.ofString s!"/opt/plugins{sep}"
  let threw ← try (do let _ ← Path.SearchPath.toBytes [evil]; pure false) catch _ => pure true
  unless threw do
    throw (IO.userError "SearchPath.toBytes wrote an entry holding the separator")
  let inner ← Path.ofString s!"/opt/a{sep}b"
  let threw2 ← try (do let _ ← Path.SearchPath.toBytes [inner]; pure false) catch _ => pure true
  unless threw2 do
    throw (IO.userError "SearchPath.toBytes wrote an entry with an embedded separator")
  -- An ordinary search path is untouched.
  let good : Path.SearchPath := [← Path.ofString "/usr/bin", ← Path.ofString "/bin"]
  unless (← Path.SearchPath.toString good) == s!"/usr/bin{sep}/bin" do
    throw (IO.userError "SearchPath.toBytes changed an ordinary search path")

/-!
`realPath` and `isSymlink` copy the path into a NUL-terminated buffer before handing it to libuv.
That copy used to be a `std::string`, whose allocation failure throws — and a C++ exception
unwinding out of an `extern "C"` frame reaches Lean-generated code with no handler for it.

Both also pass the path to the error decoder on every failure. The decoder classified some error
codes into `IO.Error` kinds that carry no filename and asserted the caller had passed none, so an
assertions-enabled build aborted on a reachable error (`EIO` from a failing disk, `ENOSYS` where
`realpath` is unavailable). It now tolerates a filename it cannot report, and supplies one of its
own when a kind requires it and the caller passed none — which `uv_cwd` does when the working
directory has been unlinked.

What this pins is that the kinds which *can* carry a filename still do.
-/
#eval show IO Unit from IO.FS.withTempDir fun dir => do
  let base ← Path.ofString dir.toString
  let file := base / Path.Filename.mk "f.txt".toByteArray
  IO.FS.writeFile (← file.toString) "hi"

  -- A missing name: `noFileOrDirectory`, which carries the filename.
  let missing := base / Path.Filename.mk "nothere".toByteArray
  try
    let _ ← (missing / Path.Filename.mk "deeper".toByteArray).resolve
    throw (IO.userError "resolve of a missing path should fail")
  catch
    | .noFileOrDirectory f _ _ =>
      unless f.endsWith "deeper" do
        throw (IO.userError s!"expected the resolved path in the error, got {f.quote}")
    | e => throw (IO.userError s!"expected noFileOrDirectory, got {e}")

  -- A name below a plain file: `ENOTDIR`, whose kind also carries the filename. Raised rather than
  -- answered `false`, since it is a question the OS declined rather than a missing name.
  try
    let _ ← (file / Path.Filename.mk "under".toByteArray).isSymlink
    throw (IO.userError "isSymlink below a file should fail")
  catch
    | .inappropriateType (some f) _ _ =>
      unless f.endsWith "under" do
        throw (IO.userError s!"expected the path in the error, got {f.quote}")
    | .inappropriateType none _ _ =>
      throw (IO.userError "inappropriateType lost the filename it can carry")
    | e => throw (IO.userError s!"expected inappropriateType, got {e}")

  -- The ordinary answers are unchanged by the buffer rewrite.
  if ← file.isSymlink then throw (IO.userError "a plain file is not a link")
  unless (← file.resolve).filename? == some (Path.Filename.mk "f.txt".toByteArray) do
    throw (IO.userError "realPath did not resolve to the file it was given")

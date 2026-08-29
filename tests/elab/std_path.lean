import Std.Path

/-!
Tests for `Std.Path` — covers parsing, rendering, structural operations, file-name helpers,
normalization, glob matching, and the `parents` iterator.
-/

open Std

-- Helpers to cut noise
private def posix (s : String) : Path := (Path.ofPosixString s).get!
private def win   (s : String) : Path := (Path.ofWindowsString s).get!


-- ---------------------------------------------------------------------------
-- Section: ofPosixString / toPosixString round-trips
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
#guard Path.ofPosixString "" = none
-- null byte → none (invalid on every platform)
#guard Path.ofPosixString "a\x00b" = none
-- ofPosixString! agrees with ofPosixString on valid input
#guard Path.ofPosixString! "/usr/local/bin" == posix "/usr/local/bin"

end PosixRoundtrip


-- ---------------------------------------------------------------------------
-- Section: ofWindowsString / toWindowsString round-trips
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
-- empty string → none (parity with ofPosixString)
#guard Path.ofWindowsString "" = none
-- null byte → none (parity with ofPosixString)
#guard Path.ofWindowsString "a\x00b" = none
-- ofWindowsString! agrees with ofWindowsString on valid input
#guard Path.ofWindowsString! "C:\\Users\\foo" == win "C:\\Users\\foo"
-- a leading "\\" introduces a prefix rather than collapsing to a root (see the Prefix section)
#guard (win "\\\\server\\share").toWindowsString = "\\\\server\\share"

end WindowsRoundtrip


-- ---------------------------------------------------------------------------
-- Section: Windows prefixes (UNC, device, verbatim)
-- ---------------------------------------------------------------------------

section Prefix

-- UNC: `\\server\share` parses as one prefix, not as a root plus two segments.
#guard (win "\\\\server\\share").winPrefix? == some "\\\\server\\share".toByteArray
#guard (win "\\\\server\\share\\dir\\file.txt").winPrefix? == some "\\\\server\\share".toByteArray
#guard (win "\\\\server\\share\\dir\\file.txt").toWindowsString = "\\\\server\\share\\dir\\file.txt"
-- a server with no share
#guard (win "\\\\server").winPrefix? == some "\\\\server".toByteArray
#guard (win "\\\\server").toWindowsString = "\\\\server"
-- forward slashes introduce a prefix too, as on Windows itself
#guard (win "//server/share/x").toWindowsString = "\\\\server\\share\\x"
-- a bare `\\` is a root, keeping `\\` and `\` equivalent
#guard (win "\\\\").winPrefix? == none
#guard (win "\\\\").toWindowsString = "\\"

-- Device namespace: `\\.\name` is captured like a UNC share, so only the first segment after
-- `\\.\` belongs to the prefix.
#guard (win "\\\\.\\COM42").winPrefix? == some "\\\\.\\COM42".toByteArray
#guard (win "\\\\.\\COM42").toWindowsString = "\\\\.\\COM42"
#guard (win "\\\\.\\pipe\\name").winPrefix? == some "\\\\.\\pipe".toByteArray
#guard (win "\\\\.\\pipe\\name").toWindowsString = "\\\\.\\pipe\\name"

-- Verbatim: the whole path after `\\?\` is the prefix, with no segments of its own.
#guard (win "\\\\?\\C:\\foo").winPrefix? == some "\\\\?\\C:\\foo".toByteArray
#guard (win "\\\\?\\C:\\foo").segments.isEmpty
#guard (win "\\\\?\\C:\\foo").toWindowsString = "\\\\?\\C:\\foo"
#guard (win "\\\\?\\cat_pics").winPrefix? == some "\\\\?\\cat_pics".toByteArray
#guard (win "\\\\?\\cat_pics").toWindowsString = "\\\\?\\cat_pics"
#guard (win "\\\\?\\UNC\\server\\share").winPrefix? == some "\\\\?\\UNC\\server\\share".toByteArray
#guard (win "\\\\?\\UNC\\server\\share").toWindowsString = "\\\\?\\UNC\\server\\share"
-- Windows normalizes nothing in a verbatim path, so neither does `normalize`, and separators and
-- repeated separators survive exactly as written.
#guard (win "\\\\?\\a\\b\\..\\c").winPrefix? == some "\\\\?\\a\\b\\..\\c".toByteArray
#guard (win "\\\\?\\a\\b\\..\\c").normalize == win "\\\\?\\a\\b\\..\\c"
#guard (win "\\\\?\\a\\.\\\\b\\").toWindowsString = "\\\\?\\a\\.\\\\b\\"
#guard (win "\\\\?\\a/b").winPrefix? == some "\\\\?\\a/b".toByteArray
-- the marker itself must be spelled with backslashes; `//?/x` is a path Windows does normalize
#guard (win "//?/x").winPrefix? == some "\\\\?\\x".toByteArray
-- the `?` and `.` markers are never re-read as a server name, even with nothing after them
#guard (win "\\\\?\\").winPrefix? == some "\\\\?\\".toByteArray
#guard (win "\\\\?\\").toWindowsString = "\\\\?\\"
#guard (win "\\\\.\\").winPrefix? == some "\\\\.".toByteArray
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
#guard (win "\\\\server\\share").parent = none
#guard (win "\\\\server\\share\\").parent = none
#guard (win "\\\\server\\share\\dir\\f").parent == some (win "\\\\server\\share\\dir")
#guard (win "\\\\server\\share\\..\\x").normalize == win "\\\\server\\share\\x"
#guard ((win "\\\\server\\share") / (win "..")).normalize == win "\\\\server\\share"
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

-- `parent` walks off the segments and stops at the anchor.
#guard ((win "C:a").parent.map Path.toWindowsString) = some "C:"
#guard ((win "C:").parent.map Path.toWindowsString) = none
#guard ((posix "/a").parent.map Path.toPosixString) = some "/"
#guard ((posix "/").parent.map Path.toPosixString) = none

-- `startsWith` compares anchors exactly, matching `endsWith` and `relativeTo?`; `\\server\share`
-- and `\\server\share\` are distinct anchors, so neither starts with the other.
#guard (posix "/a/b").startsWith (posix "/a")
#guard !(posix "/a/b").startsWith (posix "a")
#guard (win "\\\\server\\share\\a").startsWith (win "\\\\server\\share\\")
#guard !(win "\\\\server\\share\\a").startsWith (win "\\\\server\\share")

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

end Normalize


-- ---------------------------------------------------------------------------
-- Section: parent
-- ---------------------------------------------------------------------------

section Parent

-- typical case
#guard (posix "/a/b/c").parent.map (·.toPosixString) = some "/a/b"
-- one level from root
#guard (posix "/a").parent.map (·.toPosixString) = some "/"
-- root has no parent
#guard (posix "/").parent = none
-- relative single segment → "."
#guard (posix "a").parent.map (·.toPosixString) = some "."
-- relative two segments
#guard (posix "a/b").parent.map (·.toPosixString) = some "a"
-- "." is its own parent
#guard (posix ".").parent.map (·.toPosixString) = some "."
-- ".." parent
#guard (posix "..").parent.map (·.toPosixString) = some "."
-- empty path has no parent
#guard (default : Path).parent = none
-- Windows drive-relative: parent of "C:foo" is the bare drive "C:"
#guard (win "C:foo").parent.map (·.toWindowsString) = some "C:"

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
-- Section: fileName / fileStem / extension / hasExtension
-- ---------------------------------------------------------------------------

section FileInfo

-- fileName
#guard (posix "/usr/local/bin/lean").fileName = some (Path.Filename.mk "lean".toByteArray)
#guard (posix "archive.tar.gz").fileName = some (Path.Filename.mk "archive.tar.gz".toByteArray)
#guard (posix "/").fileName = none
#guard (posix "a/..").fileName = none
#guard (posix "a/.").fileName = none
#guard (default : Path).fileName = none

-- fileStem
#guard (posix "Main.lean").fileStem = some "Main".toByteArray
#guard (posix "archive.tar.gz").fileStem = some "archive.tar".toByteArray
#guard (posix "Makefile").fileStem = some "Makefile".toByteArray
#guard (posix ".gitignore").fileStem = some ".gitignore".toByteArray
#guard (posix ".hidden.lean").fileStem = some ".hidden".toByteArray
#guard (posix "/").fileStem = none

-- extension
#guard (posix "Main.lean").extension = some (Path.Extension.mk "lean".toByteArray)
#guard (posix "archive.tar.gz").extension = some (Path.Extension.mk "gz".toByteArray)
#guard (posix "Makefile").extension = none
#guard (posix ".gitignore").extension = none
#guard (posix ".hidden.lean").extension = some (Path.Extension.mk "lean".toByteArray)
#guard (posix "/").extension = none

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
-- Section: suffixes / withStem
-- ---------------------------------------------------------------------------

section Suffixes

#guard (posix "archive.tar.gz").suffixes = #["tar".toByteArray, "gz".toByteArray]
#guard (posix "foo.txt").suffixes = #["txt".toByteArray]
#guard (posix "Makefile").suffixes = #[]
#guard (posix ".gitignore").suffixes = #[]
#guard (posix ".hidden.tar.gz").suffixes = #["tar".toByteArray, "gz".toByteArray]
#guard (posix "/").suffixes = #[]

-- withStem
#guard ((posix "a/archive.tar.gz").withStem (Path.Filename.mk "backup".toByteArray)).toPosixString = "a/backup.tar.gz"
#guard ((posix "a/foo.txt").withStem (.mk "bar".toByteArray)).toPosixString = "a/bar.txt"
#guard ((posix "a/Makefile").withStem (.mk "GNUmakefile".toByteArray)).toPosixString = "a/GNUmakefile"
-- invariant: suffixes unchanged
#guard ((posix "archive.tar.gz").withStem (Path.Filename.mk "backup".toByteArray)).suffixes =
       (posix "archive.tar.gz").suffixes
-- dotfile: stem is the whole name (including dot), so withStem replaces entirely
#guard ((posix ".gitignore").withStem (.mk "profile".toByteArray)).toPosixString = "profile"
-- dotfile: withExtension appends since fileStem is the whole name and there's no extension
#guard ((posix ".gitignore").withExtension (.mk "bak".toByteArray)).toPosixString = ".gitignore.bak"

end Suffixes


-- ---------------------------------------------------------------------------
-- Section: setFileName / withFileName / withExtension / addExtension
-- ---------------------------------------------------------------------------

section Modification

-- setFileName
#guard ((posix "a/b/c").setFileName (Path.Filename.mk "d".toByteArray)).toPosixString = "a/b/d"
#guard ((posix "/").setFileName (Path.Filename.mk "d".toByteArray)).toPosixString = "/"  -- no-op on root
#guard ((posix "a/..").setFileName (Path.Filename.mk "d".toByteArray)).toPosixString = "a/.."  -- no-op on parent component
-- single-segment relative path: result has no parent prefix
#guard ((posix "foo").setFileName (Path.Filename.mk "bar".toByteArray)).toPosixString = "bar"

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
#guard ((posix "/usr/local/bin").dropPrefix? (posix "/usr/local/bin")).map (·.toPosixString) = some ""
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

-- same directory → empty relative path (renders as ""; join with base gives base)
#guard ((posix "/a/b").relativeTo? (posix "/a/b")).map (·.toPosixString) = some ""
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

end RelativeTo


-- ---------------------------------------------------------------------------
-- Section: matchGlob
-- ---------------------------------------------------------------------------

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
-- matchGlob operates on raw components and does not normalize: a literal "." segment is only matched
-- by a pattern that also has a segment there.
#guard (posix "a/./b").matchGlob "a/b" = false
#guard (posix "a/./b").matchGlob "a/*/b" = true
-- by default, a Windows drive prefix is ignored: a generic pattern matches without mentioning it,
-- and a pattern that does mention it fails (the drive component isn't there to match against)
#guard (win "C:\\Users\\foo").matchGlob "**/Users/foo" = true
#guard (win "C:\\Users\\foo").matchGlob "C:/**/Users/foo" = false
-- matchDrivePrefix := true instead requires the drive to appear as its own leading segment
#guard (win "C:\\Users\\foo").matchGlob "C:/**/Users/foo" (matchDrivePrefix := true) = true
#guard (win "C:\\Users\\foo").matchGlob "**/Users/foo" (matchDrivePrefix := true) = true
#guard (win "D:\\Users\\foo").matchGlob "C:/**/Users/foo" (matchDrivePrefix := true) = false

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
-- Section: filePrefix
-- ---------------------------------------------------------------------------

section FilePrefix

-- removes everything from first dot
#guard (posix "foo.tar.gz").filePrefix = some "foo".toByteArray
-- single extension
#guard (posix "foo.txt").filePrefix = some "foo".toByteArray
-- no extension: whole name is the prefix
#guard (posix "Makefile").filePrefix = some "Makefile".toByteArray
-- leading-dot file with no extension: whole name preserved
#guard (posix ".gitignore").filePrefix = some ".gitignore".toByteArray
-- leading-dot file with extension: leading dot kept, rest up to first dot
#guard (posix ".hidden.tar.gz").filePrefix = some ".hidden".toByteArray
#guard (posix ".hidden.lean").filePrefix = some ".hidden".toByteArray
-- no file name → none
#guard (posix "/").filePrefix = none
#guard (posix "a/..").filePrefix = none
#guard Path.empty.filePrefix = none
-- consistency with fileStem: filePrefix drops all extensions, fileStem only last
#guard (posix "a.b.c").filePrefix = some "a".toByteArray
#guard (posix "a.b.c").fileStem    = some "a.b".toByteArray

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
private def raw : Path := (Path.ofPosixBytes ("/tmp/".toByteArray ++ illFormed)).get!

-- The bytes round-trip exactly.
#guard raw.toPosixBytes == "/tmp/".toByteArray ++ illFormed
#guard raw.fileName.map (·.value) == some illFormed
#guard raw.parent.map (·.toPosixBytes) == some "/tmp".toByteArray

-- Rendering to a `String` replaces the ill-formed byte with U+FFFD.
#guard raw.toPosixString = "/tmp/a" ++ String.singleton (Char.ofNat 0xfffd) ++ "b"
#guard raw.fileName.map (·.toString) = some ("a" ++ String.singleton (Char.ofNat 0xfffd) ++ "b")

-- Globs match the decoded segment, so the ill-formed byte counts as one character.
#guard raw.matchGlob "**/a?b" = true

-- The string parsers are the byte parsers applied to the UTF-8 encoding.
#guard Path.ofPosixString "/a/b" == Path.ofPosixBytes "/a/b".toByteArray
#guard Path.ofWindowsString "C:\\a" == Path.ofWindowsBytes "C:\\a".toByteArray

-- Empty input and null bytes are rejected in byte form too.
#guard Path.ofPosixBytes ByteArray.empty == none
#guard Path.ofWindowsBytes ByteArray.empty == none
#guard Path.ofPosixBytes ⟨#[0x61, 0x00, 0x62]⟩ == none
#guard Path.ofWindowsBytes ⟨#[0x61, 0x00, 0x62]⟩ == none

-- A name that is not valid UTF-8 is still a valid `Filename` and `Extension`.
#guard (Path.Filename.ofBytes? illFormed).isSome
#guard (Path.Extension.ofBytes? illFormed).isSome
#guard Path.Filename.ofBytes? ByteArray.empty = none
#guard Path.Filename.ofBytes? "a/b".toByteArray = none

end RawBytes


-- ---------------------------------------------------------------------------
-- Section: IO boundary (pathSeparator / fromBytes / toBytes / fromString /
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

-- `fromString` / `toString` round-trip a path built from the native separator.
#eval do
  let sep ← Path.pathSeparator
  let raw := s!"{sep}usr{sep}local{sep}bin"
  let rendered ← (← Path.fromString raw).toString
  unless rendered == raw do
    throw (IO.userError s!"fromString/toString round-trip failed: {rendered}")

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

-- `fromBytes` / `toBytes` round-trip a path that no `String` can hold.
#eval do
  let sep ← Path.pathSeparator
  let rawBytes := s!"usr{sep}".toByteArray ++ illFormed
  let p ← Path.fromBytes rawBytes
  unless (← p.toBytes) == rawBytes do
    throw (IO.userError "fromBytes/toBytes round-trip lost bytes")

-- `toString` is the lossy view of the same path.
#eval do
  let sep ← Path.pathSeparator
  let p ← Path.fromBytes (s!"usr{sep}".toByteArray ++ illFormed)
  unless (← p.toString) == s!"usr{sep}a" ++ String.singleton (Char.ofNat 0xfffd) ++ "b" do
    throw (IO.userError s!"toString should replace the ill-formed byte: {← p.toString}")

-- `currentDir` reads the working directory itself.
#eval do
  unless (← Path.currentDir).isAbsolute do
    throw (IO.userError "currentDir should be absolute")

-- `resolve` hands the file name back byte for byte, over the FFI and through a name that needs
-- more than one byte per character.
#eval show IO Unit from IO.FS.withTempDir fun dir => do
  let name := Path.Filename.ofString! "caf\u00e9-\u65e5\u672c.txt"
  let dirPath ← Path.fromString dir.toString
  let file := dirPath / name
  IO.FS.writeFile (← file.toString) ""
  let resolved ← Path.resolve file
  unless resolved.fileName.map (·.value) == some name.value do
    throw (IO.userError s!"resolve mangled a non-ASCII file name: {← resolved.toString}")

-- The same, for a name that is not valid UTF-8 at all. Only a file system that accepts such a name
-- can run the check (Linux does, APFS and NTFS do not), so a name the shell failed to create is
-- skipped; once it exists, `resolve` must reproduce it exactly.
#eval show IO Unit from IO.FS.withTempDir fun dir => do
  let created ← (IO.Process.run
    { cmd := "sh", args := #["-c", s!"cd '{dir}' && touch \"$(printf 'a\\377b')\""] }).toBaseIO
  if created.isOk then
    let dirPath ← Path.fromString dir.toString
    let bad := dirPath / (Path.Filename.ofBytes? illFormed).get!
    let resolved ← Path.resolve bad
    unless resolved.fileName.map (·.value) == some illFormed do
      throw (IO.userError s!"resolve mangled a non-UTF-8 file name: {← resolved.toString}")

end IOOps

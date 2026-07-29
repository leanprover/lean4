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
#guard (win "\\\\server\\share").winPrefix? == some (.unc "server" "share")
#guard (win "\\\\server\\share\\dir\\file.txt").winPrefix? == some (.unc "server" "share")
#guard (win "\\\\server\\share\\dir\\file.txt").toWindowsString = "\\\\server\\share\\dir\\file.txt"
-- a server with no share
#guard (win "\\\\server").winPrefix? == some (.unc "server" "")
#guard (win "\\\\server").toWindowsString = "\\\\server"
-- forward slashes introduce a prefix too, as on Windows itself
#guard (win "//server/share/x").toWindowsString = "\\\\server\\share\\x"
-- a bare `\\` is a root, keeping `\\` and `\` equivalent
#guard (win "\\\\").winPrefix? == none
#guard (win "\\\\").toWindowsString = "\\"

-- Device namespace: only the first segment after `\\.\` belongs to the prefix.
#guard (win "\\\\.\\COM42").winPrefix? == some (.deviceNS "COM42")
#guard (win "\\\\.\\COM42").toWindowsString = "\\\\.\\COM42"
#guard (win "\\\\.\\pipe\\name").winPrefix? == some (.deviceNS "pipe")
#guard (win "\\\\.\\pipe\\name").toWindowsString = "\\\\.\\pipe\\name"

-- Verbatim forms.
#guard (win "\\\\?\\C:\\foo").winPrefix? == some (.verbatimDisk "C:")
#guard (win "\\\\?\\C:\\foo").toWindowsString = "\\\\?\\C:\\foo"
#guard (win "\\\\?\\cat_pics").winPrefix? == some (.verbatim "cat_pics")
#guard (win "\\\\?\\cat_pics").toWindowsString = "\\\\?\\cat_pics"
#guard (win "\\\\?\\UNC\\server\\share").winPrefix? == some (.verbatimUNC "server" "share")
#guard (win "\\\\?\\UNC\\server\\share").toWindowsString = "\\\\?\\UNC\\server\\share"
-- a verbatim segment that merely starts with "UNC" is not a verbatim UNC share
#guard (win "\\\\?\\UNCLE").winPrefix? == some (.verbatim "UNCLE")
-- the `?` and `.` markers are never re-read as a server name, even with nothing after them
#guard (win "\\\\?\\").winPrefix? == some (.verbatim "")
#guard (win "\\\\?\\").toWindowsString = "\\\\?\\"
#guard (win "\\\\.\\").winPrefix? == some (.deviceNS "")

-- Prefix predicates.
#guard (Path.Prefix.unc "server" "share").hasImplicitRoot = true
#guard (Path.Prefix.disk "C:").hasImplicitRoot = false
#guard (Path.Prefix.verbatimDisk "C:").hasImplicitRoot = false
#guard (Path.Prefix.verbatim "x").isVerbatim = true
#guard (Path.Prefix.unc "server" "share").isVerbatim = false
#guard (Path.Prefix.verbatimUNC "server" "share").drive? = none
#guard (Path.Prefix.verbatimDisk "C:").drive? = some "C:"

-- A prefix that names an absolute location is absolute with no root of its own; a drive letter is
-- not, since `C:foo` is relative to that drive's working directory.
#guard (win "\\\\server\\share").isAbsolute = true
#guard (win "\\\\.\\COM42").isAbsolute = true
#guard (win "\\\\?\\cat_pics").isAbsolute = true
#guard (win "\\\\?\\C:\\foo").isAbsolute = true
#guard (win "\\\\?\\C:foo").isAbsolute = false

-- drive? / root? / anchor across the prefix kinds.
#guard (win "\\\\server\\share").drive? = none
#guard (win "\\\\?\\C:\\foo").drive? = some "C:"
-- the root is only present when written out, so these two stay distinct
#guard (win "\\\\server\\share").root? = none
#guard (win "\\\\server\\share").anchor = "\\\\server\\share"
#guard (win "\\\\server\\share\\").root? = some "\\"
#guard (win "\\\\server\\share\\").anchor = "\\\\server\\share\\"
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
#guard (win "\\foo").isAbsolute = true    -- root without drive
#guard (posix "/usr").isRelative = false
#guard (posix "usr").isRelative = true

end Absolute


-- ---------------------------------------------------------------------------
-- Section: drive? / root? / anchor
-- ---------------------------------------------------------------------------

section Anchor

#guard (posix "/usr/bin").drive? = none
#guard (posix "/usr/bin").root? = some "/"
#guard (posix "/usr/bin").anchor = "/"
#guard (posix "a/b").drive? = none
#guard (posix "a/b").root? = none
#guard (posix "a/b").anchor = ""
#guard (win "C:\\foo").drive? = some "C:"
#guard (win "C:\\foo").root? = some "\\"
#guard (win "C:\\foo").anchor = "C:\\"
#guard (win "C:foo").drive? = some "C:"
#guard (win "C:foo").root? = none
#guard (win "C:foo").anchor = "C:"
#guard (win "\\foo").drive? = none
#guard (win "\\foo").root? = some "\\"
#guard (win "\\foo").anchor = "\\"

end Anchor


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
#guard (posix "/usr/local/bin/lean").fileName = some (Path.Filename.mk "lean")
#guard (posix "archive.tar.gz").fileName = some (Path.Filename.mk "archive.tar.gz")
#guard (posix "/").fileName = none
#guard (posix "a/..").fileName = none
#guard (posix "a/.").fileName = none
#guard (default : Path).fileName = none

-- fileStem
#guard (posix "Main.lean").fileStem = some "Main"
#guard (posix "archive.tar.gz").fileStem = some "archive.tar"
#guard (posix "Makefile").fileStem = some "Makefile"
#guard (posix ".gitignore").fileStem = some ".gitignore"
#guard (posix ".hidden.lean").fileStem = some ".hidden"
#guard (posix "/").fileStem = none

-- extension
#guard (posix "Main.lean").extension = some (Path.Extension.mk "lean")
#guard (posix "archive.tar.gz").extension = some (Path.Extension.mk "gz")
#guard (posix "Makefile").extension = none
#guard (posix ".gitignore").extension = none
#guard (posix ".hidden.lean").extension = some (Path.Extension.mk "lean")
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
#guard (Path.Filename.mk ".gitignore").isHidden = true
#guard (Path.Filename.mk "foo").isHidden = false

end FileInfo


-- ---------------------------------------------------------------------------
-- Section: Filename.ofString? / ofString! / Extension.ofString? / ofString!
-- ---------------------------------------------------------------------------

section OfString

-- Filename.ofString?
#guard Path.Filename.ofString? "lean" = some (Path.Filename.mk "lean")
#guard Path.Filename.ofString? "" = none
#guard Path.Filename.ofString? "." = none
#guard Path.Filename.ofString? ".." = none
#guard Path.Filename.ofString? "a/b" = none
#guard Path.Filename.ofString? "a\\b" = none
#guard Path.Filename.ofString? "a\x00b" = none

-- Filename.ofString!
#guard Path.Filename.ofString! "lean" = Path.Filename.mk "lean"

-- Extension.ofString?
#guard Path.Extension.ofString? "lean" = some (Path.Extension.mk "lean")
#guard Path.Extension.ofString? "" = none
#guard Path.Extension.ofString? "a.b" = none
#guard Path.Extension.ofString? "a/b" = none
#guard Path.Extension.ofString? "a\\b" = none
#guard Path.Extension.ofString? "a\x00b" = none

-- Extension.ofString!
#guard Path.Extension.ofString! "lean" = Path.Extension.mk "lean"

end OfString


-- ---------------------------------------------------------------------------
-- Section: Ord instances (Filename, Extension, Path)
-- ---------------------------------------------------------------------------

section OrdInstances

#guard compare (Path.Filename.mk "a") (Path.Filename.mk "b") = Ordering.lt
#guard compare (Path.Filename.mk "b") (Path.Filename.mk "a") = Ordering.gt
#guard compare (Path.Filename.mk "a") (Path.Filename.mk "a") = Ordering.eq

#guard compare (Path.Extension.mk "gz") (Path.Extension.mk "tar") = Ordering.lt
#guard compare (Path.Extension.mk "tar") (Path.Extension.mk "tar") = Ordering.eq

#guard compare (posix "a") (posix "b") = Ordering.lt
#guard compare (posix "a/b") (posix "a") = Ordering.gt  -- longer array, common prefix
#guard compare (posix "a") (posix "a") = Ordering.eq

-- sorting a list of paths
#guard ((#[posix "c", posix "a", posix "b"]).qsort (compare · · = .lt) |>.map (·.toPosixString)) = #["a", "b", "c"]

end OrdInstances


-- ---------------------------------------------------------------------------
-- Section: suffixes / withStem
-- ---------------------------------------------------------------------------

section Suffixes

#guard (posix "archive.tar.gz").suffixes = #["tar", "gz"]
#guard (posix "foo.txt").suffixes = #["txt"]
#guard (posix "Makefile").suffixes = #[]
#guard (posix ".gitignore").suffixes = #[]
#guard (posix ".hidden.tar.gz").suffixes = #["tar", "gz"]
#guard (posix "/").suffixes = #[]

-- withStem
#guard ((posix "a/archive.tar.gz").withStem (Path.Filename.mk "backup")).toPosixString = "a/backup.tar.gz"
#guard ((posix "a/foo.txt").withStem (.mk "bar")).toPosixString = "a/bar.txt"
#guard ((posix "a/Makefile").withStem (.mk "GNUmakefile")).toPosixString = "a/GNUmakefile"
-- invariant: suffixes unchanged
#guard ((posix "archive.tar.gz").withStem (Path.Filename.mk "backup")).suffixes =
       (posix "archive.tar.gz").suffixes
-- dotfile: stem is the whole name (including dot), so withStem replaces entirely
#guard ((posix ".gitignore").withStem (.mk "profile")).toPosixString = "profile"
-- dotfile: withExtension appends since fileStem is the whole name and there's no extension
#guard ((posix ".gitignore").withExtension (.mk "bak")).toPosixString = ".gitignore.bak"

end Suffixes


-- ---------------------------------------------------------------------------
-- Section: setFileName / withFileName / withExtension / addExtension
-- ---------------------------------------------------------------------------

section Modification

-- setFileName
#guard ((posix "a/b/c").setFileName (Path.Filename.mk "d")).toPosixString = "a/b/d"
#guard ((posix "/").setFileName (Path.Filename.mk "d")).toPosixString = "/"  -- no-op on root
#guard ((posix "a/..").setFileName (Path.Filename.mk "d")).toPosixString = "a/.."  -- no-op on parent component
-- single-segment relative path: result has no parent prefix
#guard ((posix "foo").setFileName (Path.Filename.mk "bar")).toPosixString = "bar"

-- withExtension
#guard ((posix "a/b.tar.gz").withExtension (Path.Extension.mk "xz")).toPosixString = "a/b.tar.xz"
#guard ((posix "a/b.txt").withExtension (Path.Extension.mk "lean")).toPosixString = "a/b.lean"
#guard ((posix "a/Makefile").withExtension (Path.Extension.mk "bak")).toPosixString = "a/Makefile.bak"
#guard ((posix "/").withExtension (Path.Extension.mk "bak")).toPosixString = "/"  -- no-op

-- addExtension
#guard ((posix "a/b.tar.gz").addExtension (Path.Extension.mk "bak")).toPosixString = "a/b.tar.gz.bak"
#guard ((posix "a/Makefile").addExtension (Path.Extension.mk "bak")).toPosixString = "a/Makefile.bak"
#guard ((posix "/").addExtension (Path.Extension.mk "bak")).toPosixString = "/"  -- no-op

-- removeExtension
#guard ((posix "a/b.tar.gz").removeExtension).toPosixString = "a/b.tar"  -- only the last extension
#guard ((posix "a/b.txt").removeExtension).toPosixString = "a/b"
#guard ((posix "a/Makefile").removeExtension).toPosixString = "a/Makefile"  -- no extension: no-op
#guard ((posix ".gitignore").removeExtension).toPosixString = ".gitignore"  -- dotfile: no-op
#guard ((posix ".hidden.lean").removeExtension).toPosixString = ".hidden"
#guard ((posix "/").removeExtension).toPosixString = "/"  -- no file name: no-op
-- inverse of addExtension
#guard ((posix "a/b.txt").addExtension (Path.Extension.mk "bak") |>.removeExtension).toPosixString = "a/b.txt"

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
-- a relative suffix matches whole components from the back, even just behind the root (matches Rust)
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

-- empty has no components
#guard Path.empty.components = #[]
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
-- Windows root without drive
#guard (win "\\").isRoot = true
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
-- Section: depth
-- ---------------------------------------------------------------------------

section Depth

-- typical absolute paths
#guard (posix "/usr/local/bin").depth = 3
#guard (posix "/usr").depth = 1
-- root only: no normal components
#guard (posix "/").depth = 0
-- relative paths
#guard (posix "a/b/c").depth = 3
#guard (posix "a").depth = 1
-- special components do not count
#guard (posix "..").depth = 0
#guard (posix ".").depth = 0
-- mixed: "a" and "b" are normal, ".." is not
#guard (posix "a/../b").depth = 2
-- empty path
#guard Path.empty.depth = 0
-- Windows
#guard (win "C:\\Users\\foo\\bar").depth = 3

end Depth


-- ---------------------------------------------------------------------------
-- Section: filePrefix
-- ---------------------------------------------------------------------------

section FilePrefix

-- removes everything from first dot
#guard (posix "foo.tar.gz").filePrefix = some "foo"
-- single extension
#guard (posix "foo.txt").filePrefix = some "foo"
-- no extension: whole name is the prefix
#guard (posix "Makefile").filePrefix = some "Makefile"
-- leading-dot file with no extension: whole name preserved
#guard (posix ".gitignore").filePrefix = some ".gitignore"
-- leading-dot file with extension: leading dot kept, rest up to first dot
#guard (posix ".hidden.tar.gz").filePrefix = some ".hidden"
#guard (posix ".hidden.lean").filePrefix = some ".hidden"
-- no file name → none
#guard (posix "/").filePrefix = none
#guard (posix "a/..").filePrefix = none
#guard Path.empty.filePrefix = none
-- consistency with fileStem: filePrefix drops all extensions, fileStem only last
#guard (posix "a.b.c").filePrefix = some "a"
#guard (posix "a.b.c").fileStem    = some "a.b"

end FilePrefix


-- ---------------------------------------------------------------------------
-- Section: IO boundary (pathSeparator / fromString / toString / toAbsoluteCwd /
-- resolve). These exercise the platform-native rendering path and the
-- `lean_uv_realpath` FFI binding. Assertions are written to hold on both POSIX
-- and Windows hosts.
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

-- `toAbsoluteCwd` turns a relative path into an absolute one, keeping the tail.
#eval do
  let abs ← Path.toAbsoluteCwd (posix "a/b")
  unless abs.isAbsolute do
    throw (IO.userError "toAbsoluteCwd should produce an absolute path")
  unless abs.endsWith (posix "a/b") do
    throw (IO.userError s!"toAbsoluteCwd dropped the relative tail: {← abs.toString}")

-- `toAbsoluteCwd` is a no-op on an already-absolute path.
#eval do
  let p := posix "/usr/local"
  unless (← Path.toAbsoluteCwd p) == p do
    throw (IO.userError "toAbsoluteCwd should leave absolute paths unchanged")

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

end IOOps

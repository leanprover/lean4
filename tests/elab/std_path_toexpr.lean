import Lean
import Std.Path

/-!
Tests for `ToExpr Std.Path` (and the `Path.Anchor`, `Path.Segment` and `ByteArray` instances it is
built from).

The property under test is that a quoted path denotes the path it was quoted from *exactly*, not
just up to `==`: a term baked into an `.olean` on one platform has to read back as the same path on
another, which is what `System.FilePath`'s instance cannot promise because it emits a bare string
that the reading platform reinterprets with its own separator rules.

Silent on success; every failure throws.
-/

open Lean Meta Std

private unsafe def evalPathUnsafe (e : Expr) : MetaM Path :=
  evalExpr Path (mkConst ``Std.Path) e

@[implemented_by evalPathUnsafe]
private opaque evalPath (e : Expr) : MetaM Path

private def posix (s : String) : Path := Path.ofPosixString! s
private def win (s : String) : Path := Path.ofWindowsString! s

/-- Paths whose quotation must round-trip, paired with the constant the term is expected to name. -/
private def cases : List (String × Path × Name) :=
  [ ("empty", Path.empty, ``Path.empty)
  , ("relative posix", posix "src/Main.lean", ``Path.ofPosixString!)
  , ("absolute posix", posix "/usr/local/bin", ``Path.ofPosixString!)
  , ("dot segments", posix "a/./b/../c", ``Path.ofPosixString!)
  , ("drive", win "C:\\Users\\me\\Main.lean", ``Path.ofWindowsString!)
  , ("rootless drive", win "C:foo", ``Path.ofWindowsString!)
  , ("UNC share", win "\\\\server\\share\\a", ``Path.ofWindowsString!)
  , ("verbatim", win "\\\\?\\C:\\a/b", ``Path.ofWindowsString!)
  , ("bare windows root", win "\\foo", ``Path.ofWindowsString!)
    -- No string literal holds these bytes, and no render of these segments reads back as itself,
    -- so both fall through to the structural form.
  , ("non-UTF-8 bytes", (Path.ofPosixBytes? (ByteArray.mk #[0x61, 0xff, 0x62])).get!, ``Path.ofParts)
  , ("segment the flavour cannot spell", win "C:\\a" / posix "b\\c", ``Path.ofParts)
  ]

run_meta do
  for (name, p, expected) in cases do
    let e := toExpr p
    let head := e.getAppFn.constName?
    unless head == some expected do
      throwError "{name}: expected the term to name {expected}, got {head}"
    let p' ← evalPath e
    unless p' = p do
      throwError "{name}: quoting is not faithful\n  before: {repr p}\n  after:  {repr p'}"

-- A Windows path keeps its flavour in the term, so the reading platform cannot reinterpret it.
run_meta do
  let p := win "C:\\Users\\me\\Main.lean"
  let p' ← evalPath (toExpr p)
  unless p'.anchor = p.anchor && p'.isAbsolute && p'.components.size == 3 do
    throwError "windows path lost its anchor: {repr p'}"

-- By contrast, `System.FilePath` quotes to a string with nothing recording the flavour.
run_meta do
  let e := toExpr (System.FilePath.mk "C:\\Users\\me\\Main.lean")
  unless e.getAppFn.constName? == some ``System.FilePath.mk && e.appArg!.isLit do
    throwError "expected `FilePath.mk <string literal>`, got {e}"

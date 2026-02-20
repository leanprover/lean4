module
import Lean.Compiler.NameMangling
import Lean.Compiler.NameDemangling

/-!
# Tests for Lean Name Demangling

Tests the full demangling pipeline from `NameDemangling.lean`.
-/

open Lean.Name.Demangle
open Lean (Name)

def check (label : String) (got expected : String) : IO Unit := do
  if got != expected then
    throw <| .userError s!"FAIL [{label}]: got {repr got}, expected {repr expected}"

def checkSome (label : String) (got : Option String) (expected : String) : IO Unit := do
  match got with
  | some v => check label v expected
  | none => throw <| .userError s!"FAIL [{label}]: got none, expected {repr expected}"

def checkNone (label : String) (got : Option String) : IO Unit := do
  match got with
  | some v => throw <| .userError s!"FAIL [{label}]: got {repr v}, expected none"
  | none => pure ()

def checkName (label : String) (got expected : Name) : IO Unit := do
  if got != expected then
    throw <| .userError s!"FAIL [{label}]: got {repr got}, expected {repr expected}"

-- Helper to build name with compiler suffixes
private def mkName (parts : List (String ⊕ Nat)) : Name :=
  parts.foldl (fun n p =>
    match p with
    | .inl s => n.str s
    | .inr k => n.num k) .anonymous

-- Verify mangle → demangle round-trips: demangle(mangle(name)) == name
private def checkRoundTrip (label : String) (parts : List (String ⊕ Nat)) : IO Unit := do
  let name := mkName parts
  let mangled := name.mangle ""
  let demangled := Name.demangle mangled
  checkName s!"roundtrip {label}" demangled name

-- ============================================================================
-- String.mangle
-- ============================================================================

#eval check "mangle alphanumeric" (String.mangle "hello") "hello"
#eval check "mangle underscore" (String.mangle "a_b") "a__b"
#eval check "mangle double underscore" (String.mangle "__") "____"
#eval check "mangle dot" (String.mangle ".") "_x2e"
#eval check "mangle a.b" (String.mangle "a.b") "a_x2eb"
#eval check "mangle lambda" (String.mangle "\u03bb") "_u03bb"
#eval check "mangle astral" (String.mangle (String.singleton (Char.ofNat 0x1d55c))) "_U0001d55c"
#eval check "mangle empty" (String.mangle "") ""

-- ============================================================================
-- Name.mangle
-- ============================================================================

#eval check "mangle simple name" (Name.mangle `Lean.Meta.Sym.main) "l_Lean_Meta_Sym_main"
#eval check "mangle single" (Name.mangle `main) "l_main"
#eval check "mangle underscore comp" (Name.mangle `a_b) "l_a__b"
#eval check "mangle underscore comp.c" (Name.mangle `a_b.c) "l_a__b_c"
#eval do
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "withMVarContextImp"]
  check "mangle private" (name.mangle "l_")
    "l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp"
#eval do
  let name := mkName [.inr 42]
  check "mangle numeric root" (name.mangle "l_") "l_42_"
#eval do
  let name := mkName [.inr 42, .inl "foo"]
  check "mangle numeric root + str" (name.mangle "l_") "l_42__foo"
#eval do
  let name := mkName [.inl "a", .inl "x27"]
  check "mangle disambiguation" (name.mangle "l_") "l_a_00x27"
#eval do
  let name := mkName [.inl "0foo"]
  check "mangle digit start disambiguation" (name.mangle "l_") "l_000foo"
#eval do
  check "mangle custom prefix" (Name.mangle `foo "lp_pkg_") "lp_pkg_foo"

-- ============================================================================
-- Name.demangle (core algorithm, no postprocessing)
-- ============================================================================

#eval checkName "demangle simple" (Name.demangle "Lean_Meta_Sym_main") `Lean.Meta.Sym.main
#eval checkName "demangle single" (Name.demangle "main") `main
#eval checkName "demangle underscore" (Name.demangle "a__b") `a_b
#eval checkName "demangle underscore multi" (Name.demangle "a__b_c") `a_b.c
#eval checkName "demangle numeric"
  (Name.demangle "foo_42__bar") (mkName [.inl "foo", .inr 42, .inl "bar"])
#eval checkName "demangle numeric root"
  (Name.demangle "42_") (mkName [.inr 42])
#eval checkName "demangle numeric at end"
  (Name.demangle "foo_42_") (mkName [.inl "foo", .inr 42])
#eval checkName "demangle disambiguation 00"
  (Name.demangle "a_00x27") (mkName [.inl "a", .inl "x27"])
#eval checkName "demangle disambiguation root"
  (Name.demangle "000foo") (mkName [.inl "0foo"])
#eval checkName "demangle hex x"
  (Name.demangle "a_x2eb") (mkName [.inl "a.b"])
#eval checkName "demangle hex u"
  (Name.demangle "_u03bb") (mkName [.inl "\u03bb"])
#eval checkName "demangle hex U"
  (Name.demangle "_U0001d55c") (mkName [.inl (String.singleton (Char.ofNat 0x1d55c))])
#eval checkName "demangle private"
  (Name.demangle "__private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp")
  (mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
           .inr 0, .inl "Lean", .inl "Meta", .inl "withMVarContextImp"])
#eval checkName "demangle boxed suffix"
  (Name.demangle "foo___boxed") (mkName [.inl "foo", .inl "_boxed"])
#eval checkName "demangle underscore-ending component"
  (Name.demangle "a___00b") (mkName [.inl "a_", .inl "b"])

-- ============================================================================
-- Mangle/demangle round-trips
-- ============================================================================

#eval checkRoundTrip "simple" [.inl "Lean", .inl "Meta", .inl "main"]
#eval checkRoundTrip "single" [.inl "a"]
#eval checkRoundTrip "three" [.inl "Foo", .inl "Bar", .inl "baz"]
#eval checkRoundTrip "numeric" [.inl "foo", .inr 0, .inl "bar"]
#eval checkRoundTrip "numeric root" [.inr 42]
#eval checkRoundTrip "numeric multi" [.inl "a", .inr 1, .inl "b", .inr 2, .inl "c"]
#eval checkRoundTrip "_private" [.inl "_private"]
#eval checkRoundTrip "underscore" [.inl "a_b", .inl "c_d"]
#eval checkRoundTrip "_at_ _spec" [.inl "_at_", .inl "_spec"]
#eval checkRoundTrip "private name"
  [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic", .inr 0,
   .inl "Lean", .inl "Meta", .inl "withMVarContextImp"]
#eval checkRoundTrip "boxed" [.inl "Lean", .inl "Meta", .inl "foo", .inl "_boxed"]
#eval checkRoundTrip "redArg" [.inl "Lean", .inl "Meta", .inl "foo", .inl "_redArg"]
#eval checkRoundTrip "specialization"
  [.inl "List", .inl "map", .inl "_at_", .inl "Foo", .inl "bar", .inl "_spec", .inr 3]
#eval checkRoundTrip "lambda" [.inl "Foo", .inl "bar", .inl "_lambda", .inr 0]
#eval checkRoundTrip "lambda 2" [.inl "Foo", .inl "bar", .inl "_lambda", .inr 2]
#eval checkRoundTrip "closed" [.inl "myConst", .inl "_closed", .inr 0]
#eval checkRoundTrip "dot char" [.inl "a.b"]
#eval checkRoundTrip "unicode" [.inl "\u03bb"]
#eval checkRoundTrip "unicode arrow" [.inl "a", .inl "b\u2192c"]
#eval checkRoundTrip "disambiguation x27" [.inl "a", .inl "x27"]
#eval checkRoundTrip "disambiguation 0foo" [.inl "0foo"]
#eval checkRoundTrip "disambiguation underscore end" [.inl "a_", .inl "b"]
#eval checkRoundTrip "complex"
  [.inl "Lean", .inl "MVarId", .inl "withContext", .inl "_at_",
   .inl "_private", .inl "Lean", .inl "Meta", .inl "Sym", .inr 0,
   .inl "Lean", .inl "Meta", .inl "Sym", .inl "BackwardRule", .inl "apply",
   .inl "_spec", .inr 2, .inl "_redArg", .inl "_lambda", .inr 0, .inl "_boxed"]

-- ============================================================================
-- Basic l_ prefix demangling
-- ============================================================================

#eval checkSome "simple l_" (demangleSymbol "l_Lean_Meta_Sym_main") "Lean.Meta.Sym.main"
#eval checkSome "single l_" (demangleSymbol "l_main") "main"

-- ============================================================================
-- lp_ prefix with package names
-- ============================================================================

#eval do
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "std"}_")
  checkSome "lp_ simple" (demangleSymbol mangled) "Lean.Meta.foo (std)"

#eval do
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "my_pkg"}_")
  checkSome "lp_ underscore pkg" (demangleSymbol mangled) "Lean.Meta.foo (my_pkg)"

#eval do
  let name := mkName [.inl "_private", .inl "X", .inr 0, .inl "Y", .inl "foo"]
  let mangled := name.mangle (s!"lp_{String.mangle "pkg"}_")
  checkSome "lp_ private decl" (demangleSymbol mangled) "Y.foo [private] (pkg)"

-- ============================================================================
-- _init_ prefixes
-- ============================================================================

#eval checkSome "init l_"
  (demangleSymbol "_init_l_Lean_Meta_foo") "[init] Lean.Meta.foo"

#eval do
  let name := mkName [.inl "_private", .inl "X", .inr 0, .inl "Y", .inl "foo"]
  let mangled := "_init_" ++ name.mangle "l_"
  checkSome "init l_ private" (demangleSymbol mangled) "[init] Y.foo [private]"

#eval do
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "std"}_")
  checkSome "init lp_" (demangleSymbol ("_init_" ++ mangled))
    "[init] Lean.Meta.foo (std)"

-- ============================================================================
-- initialize_ prefixes
-- ============================================================================

#eval checkSome "initialize bare"
  (demangleSymbol "initialize_Init_Control_Basic") "[module_init] Init.Control.Basic"
#eval checkSome "initialize l_"
  (demangleSymbol "initialize_l_Lean_Meta_foo") "[module_init] Lean.Meta.foo"

#eval do
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "std"}_")
  checkSome "initialize lp_" (demangleSymbol ("initialize_" ++ mangled))
    "[module_init] Lean.Meta.foo (std)"

-- ============================================================================
-- lean_apply_N and _lean_main
-- ============================================================================

#eval checkSome "lean_apply_5" (demangleSymbol "lean_apply_5") "<apply/5>"
#eval checkSome "lean_apply_12" (demangleSymbol "lean_apply_12") "<apply/12>"
#eval checkSome "lean_main" (demangleSymbol "_lean_main") "[lean] main"

-- ============================================================================
-- .cold.N suffix handling
-- ============================================================================

#eval do
  let mangled := Name.mangle `Lean.Meta.foo._redArg "l_"
  checkSome "cold suffix" (demangleSymbol (mangled ++ ".cold.1"))
    "Lean.Meta.foo [arity↓] .cold.1"

#eval checkSome "cold suffix plain"
  (demangleSymbol "l_Lean_Meta_foo.cold") "Lean.Meta.foo .cold"

#eval checkSome "cold lean_apply"
  (demangleSymbol "lean_apply_5.cold.1") "<apply/5> .cold.1"

#eval checkSome "cold lean_main"
  (demangleSymbol "_lean_main.cold.1") "[lean] main .cold.1"

-- ============================================================================
-- Non-Lean symbols return none
-- ============================================================================

#eval checkNone "printf" (demangleSymbol "printf")
#eval checkNone "malloc" (demangleSymbol "malloc")
#eval checkNone "empty" (demangleSymbol "")

-- ============================================================================
-- Postprocessing: suffix folding
-- ============================================================================

#eval do
  let name := mkName [.inl "foo", .inl "_boxed"]
  checkSome "boxed" (demangleSymbol (name.mangle "l_")) "foo [boxed]"

#eval do
  let name := mkName [.inl "foo", .inl "_redArg"]
  checkSome "redArg" (demangleSymbol (name.mangle "l_")) "foo [arity↓]"

#eval do
  let name := mkName [.inl "foo", .inl "_impl"]
  checkSome "impl" (demangleSymbol (name.mangle "l_")) "foo [impl]"

#eval do
  let name := mkName [.inl "foo", .inl "_lam", .inr 0]
  checkSome "lambda separate" (demangleSymbol (name.mangle "l_")) "foo [λ]"

#eval do
  let name := mkName [.inl "foo", .inl "_lam_0"]
  checkSome "lambda indexed" (demangleSymbol (name.mangle "l_")) "foo [λ]"

#eval do
  let name := mkName [.inl "foo", .inl "_lambda_2"]
  checkSome "lambda_2" (demangleSymbol (name.mangle "l_")) "foo._lambda_2"

#eval do
  let name := mkName [.inl "foo", .inl "_elam"]
  checkSome "elam" (demangleSymbol (name.mangle "l_")) "foo [λ]"

#eval do
  let name := mkName [.inl "foo", .inl "_elam_1"]
  checkSome "elam indexed" (demangleSymbol (name.mangle "l_")) "foo [λ]"

#eval do
  let name := mkName [.inl "foo", .inl "_jp"]
  checkSome "jp" (demangleSymbol (name.mangle "l_")) "foo [jp]"

#eval do
  let name := mkName [.inl "foo", .inl "_jp_3"]
  checkSome "jp indexed" (demangleSymbol (name.mangle "l_")) "foo._jp_3"

#eval do
  let name := mkName [.inl "myConst", .inl "_closed", .inr 0]
  checkSome "closed" (demangleSymbol (name.mangle "l_")) "myConst [closed]"

#eval do
  let name := mkName [.inl "myConst", .inl "_closed_0"]
  checkSome "closed indexed" (demangleSymbol (name.mangle "l_")) "myConst._closed_0"

#eval do
  let name := mkName [.inl "foo", .inl "_redArg", .inl "_boxed"]
  checkSome "multiple suffixes" (demangleSymbol (name.mangle "l_"))
    "foo [boxed, arity↓]"

#eval do
  -- _lam_0 followed by _boxed
  let name := mkName [.inl "Lean", .inl "Meta", .inl "Simp", .inl "simpLambda",
                       .inl "_lam_0", .inl "_boxed"]
  checkSome "lambda + boxed" (demangleSymbol (name.mangle "l_"))
    "Lean.Meta.Simp.simpLambda [boxed, λ]"

#eval do
  -- _redArg followed by _lam_0
  let name := mkName [.inl "Lean", .inl "profileitIOUnsafe",
                       .inl "_redArg", .inl "_lam_0"]
  checkSome "redArg + lam" (demangleSymbol (name.mangle "l_"))
    "Lean.profileitIOUnsafe [λ, arity↓]"

-- ============================================================================
-- Postprocessing: private name stripping
-- ============================================================================

#eval do
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "foo"]
  checkSome "private" (demangleSymbol (name.mangle "l_"))
    "Lean.Meta.foo [private]"

#eval do
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "foo", .inl "_redArg"]
  checkSome "private + redArg" (demangleSymbol (name.mangle "l_"))
    "Lean.Meta.foo [arity↓, private]"

-- ============================================================================
-- Postprocessing: hygienic suffix stripping
-- ============================================================================

#eval do
  let name := mkName [.inl "Lean", .inl "Meta", .inl "foo", .inl "_@",
                       .inl "Lean", .inl "Meta", .inl "_hyg", .inr 42]
  checkSome "hygienic strip" (demangleSymbol (name.mangle "l_"))
    "Lean.Meta.foo"

-- ============================================================================
-- Postprocessing: specialization contexts
-- ============================================================================

#eval do
  let name := mkName [.inl "List", .inl "map", .inl "_at_",
                       .inl "Foo", .inl "bar", .inl "_spec", .inr 3]
  checkSome "specialization" (demangleSymbol (name.mangle "l_"))
    "List.map spec at Foo.bar"

#eval do
  let name := mkName [.inl "Lean", .inl "MVarId", .inl "withContext",
                       .inl "_at_", .inl "Foo", .inl "bar", .inl "_spec", .inr 2,
                       .inl "_boxed"]
  checkSome "spec with base suffix" (demangleSymbol (name.mangle "l_"))
    "Lean.MVarId.withContext [boxed] spec at Foo.bar"

#eval do
  let name := mkName [.inl "Lean", .inl "Meta", .inl "foo",
                       .inl "_at_", .inl "Lean", .inl "Meta", .inl "bar",
                       .inl "_elam_1", .inl "_redArg", .inl "_spec", .inr 2]
  checkSome "spec context flags" (demangleSymbol (name.mangle "l_"))
    "Lean.Meta.foo spec at Lean.Meta.bar[λ, arity↓]"

#eval do
  -- Duplicate flag labels are deduplicated: _lam_0 + _elam_1 both map to λ
  let name := mkName [.inl "f", .inl "_at_",
                       .inl "g", .inl "_lam_0", .inl "_elam_1", .inl "_redArg",
                       .inl "_spec", .inr 1]
  checkSome "spec context flags dedup" (demangleSymbol (name.mangle "l_"))
    "f spec at g[λ, arity↓]"

#eval do
  let name := mkName [.inl "f",
                       .inl "_at_", .inl "g", .inl "_spec", .inr 1,
                       .inl "_at_", .inl "h", .inl "_spec", .inr 2]
  checkSome "multiple at" (demangleSymbol (name.mangle "l_"))
    "f spec at g spec at h"

#eval do
  -- Multiple spec at with flags on base and contexts
  let name := mkName [.inl "f",
                       .inl "_at_", .inl "g", .inl "_redArg", .inl "_spec", .inr 1,
                       .inl "_at_", .inl "h", .inl "_lam_0", .inl "_spec", .inr 2,
                       .inl "_boxed"]
  checkSome "multiple at with flags" (demangleSymbol (name.mangle "l_"))
    "f [boxed] spec at g[arity↓] spec at h[λ]"

#eval do
  -- Base trailing suffix appearing after _spec N
  let name := mkName [.inl "f", .inl "_at_", .inl "g", .inl "_spec", .inr 1,
                       .inl "_lam_0"]
  checkSome "base flags after spec" (demangleSymbol (name.mangle "l_"))
    "f [λ] spec at g"

#eval do
  -- spec_0 entries in context should be stripped
  let name := mkName [.inl "Lean", .inl "Meta", .inl "transformWithCache", .inl "visit",
                       .inl "_at_",
                       .inl "_private", .inl "Lean", .inl "Meta", .inl "Transform", .inr 0,
                       .inl "Lean", .inl "Meta", .inl "transform",
                       .inl "Lean", .inl "Meta", .inl "Sym", .inl "unfoldReducible",
                       .inl "spec_0", .inl "spec_0",
                       .inl "_spec", .inr 1]
  checkSome "spec context strip spec_0" (demangleSymbol (name.mangle "l_"))
    "Lean.Meta.transformWithCache.visit spec at Lean.Meta.transform.Lean.Meta.Sym.unfoldReducible"

#eval do
  -- _private in spec context should be stripped
  let name := mkName [.inl "Array", .inl "mapMUnsafe", .inl "map",
                       .inl "_at_",
                       .inl "_private", .inl "Lean", .inl "Meta", .inl "Transform", .inr 0,
                       .inl "Lean", .inl "Meta", .inl "transformWithCache", .inl "visit",
                       .inl "_spec", .inr 1]
  checkSome "spec context strip private" (demangleSymbol (name.mangle "l_"))
    "Array.mapMUnsafe.map spec at Lean.Meta.transformWithCache.visit"

-- ============================================================================
-- Complex real-world name
-- ============================================================================

#eval do
  let name := mkName [.inl "Lean", .inl "MVarId", .inl "withContext",
                       .inl "_at_",
                       .inl "_private", .inl "Lean", .inl "Meta", .inl "Sym", .inr 0,
                       .inl "Lean", .inl "Meta", .inl "Sym", .inl "BackwardRule", .inl "apply",
                       .inl "_spec", .inr 2,
                       .inl "_redArg", .inl "_lambda", .inr 0, .inl "_boxed"]
  checkSome "complex" (demangleSymbol (name.mangle "l_"))
    "Lean.MVarId.withContext [boxed, λ, arity↓] spec at Lean.Meta.Sym.BackwardRule.apply"

-- ============================================================================
-- Backtrace line parsing: Linux glibc format
-- ============================================================================

#eval checkSome "bt linux"
  (demangleBtLine "./lean(l_Lean_Meta_foo+0x2a) [0x555555555555]")
  "./lean(Lean.Meta.foo+0x2a) [0x555555555555]"

#eval do
  let name := mkName [.inl "foo", .inl "_boxed"]
  let sym := name.mangle "l_"
  checkSome "bt linux boxed"
    (demangleBtLine s!"./lean({sym}+0x10) [0x7fff]")
    "./lean(foo [boxed]+0x10) [0x7fff]"

#eval do
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "foo"]
  let sym := name.mangle "l_"
  checkSome "bt linux private"
    (demangleBtLine s!"./lean({sym}+0x10) [0x7fff]")
    "./lean(Lean.Meta.foo [private]+0x10) [0x7fff]"

#eval do
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "foo", .inl "_redArg"]
  let sym := name.mangle "l_"
  checkSome "bt linux private + redArg"
    (demangleBtLine s!"./lean({sym}+0x10) [0x7fff]")
    "./lean(Lean.Meta.foo [arity↓, private]+0x10) [0x7fff]"

-- ============================================================================
-- Backtrace line parsing: macOS format
-- ============================================================================

#eval checkSome "bt macos"
  (demangleBtLine "3   lean   0x00000001001234 l_Lean_Meta_foo + 42")
  "3   lean   0x00000001001234 Lean.Meta.foo + 42"

#eval do
  let name := mkName [.inl "foo", .inl "_redArg"]
  let sym := name.mangle "l_"
  checkSome "bt macos redArg"
    (demangleBtLine s!"3   lean   0x00000001001234 {sym} + 42")
    "3   lean   0x00000001001234 foo [arity↓] + 42"

-- ============================================================================
-- Backtrace line parsing: non-Lean lines unchanged
-- ============================================================================

#eval checkNone "bt non-lean"
  (demangleBtLine "./lean(printf+0x10) [0x7fff]")

#eval checkNone "bt no parens"
  (demangleBtLine "just some random text")

-- ============================================================================
-- Edge cases: never crashes
-- ============================================================================

#eval do
  let inputs := #[
    "", "l_", "lp_", "lp_x", "_init_", "initialize_",
    "l_____", "lp____", "l_00", "l_0",
    "some random string", "l_ space",
    "_init_l_", "_init_lp_", "_init_lp_x",
    "initialize_l_", "initialize_lp_", "initialize_lp_x",
    "lean_apply_", "lean_apply_x", "lean_apply_0",
    "l_x", "l_0", "l_00", "l___", "lp_a_b",
    ".cold", ".cold.1", "l_.cold", "l_x.cold.99"
  ]
  inputs.forM fun inp => do
    let _ := demangleSymbol inp
    let _ := demangleBtLine inp
    pure ()

-- ============================================================================
-- C export wrappers
-- ============================================================================

#eval check "export symbol"
  ((demangleSymbol "l_Lean_Meta_foo").getD "") "Lean.Meta.foo"
#eval check "export symbol none"
  ((demangleSymbol "printf").getD "") ""
#eval check "export bt line"
  ((demangleBtLine "./lean(l_foo+0x1) [0x2]").getD "") "./lean(foo+0x1) [0x2]"
#eval check "export bt line none"
  ((demangleBtLine "no lean symbols here").getD "") ""

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

-- Helper to build name with compiler suffixes
private def mkName (parts : List (String ⊕ Nat)) : Name :=
  parts.foldl (fun n p =>
    match p with
    | .inl s => n.str s
    | .inr k => n.num k) .anonymous

-- ============================================================================
-- Basic l_ prefix demangling
-- ============================================================================

#eval checkSome "simple l_" (demangleSymbol "l_Lean_Meta_Sym_main") "Lean.Meta.Sym.main"
#eval checkSome "single l_" (demangleSymbol "l_main") "main"

-- ============================================================================
-- lp_ prefix with package names
-- ============================================================================

#eval do
  -- Construct: lp_std_Lean_Meta_foo
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "std"}_")
  checkSome "lp_ simple" (demangleSymbol mangled) "Lean.Meta.foo (std)"

#eval do
  -- Package with underscore: my_pkg
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "my_pkg"}_")
  checkSome "lp_ underscore pkg" (demangleSymbol mangled) "Lean.Meta.foo (my_pkg)"

-- ============================================================================
-- _init_ prefixes
-- ============================================================================

#eval checkSome "init l_"
  (demangleSymbol "_init_l_Lean_Meta_foo") "[init] Lean.Meta.foo"

#eval do
  let name := mkName [.inl "_private", .inl "X", .inr 0, .inl "Y", .inl "foo"]
  let mangled := "_init_" ++ name.mangle "l_"
  checkSome "init l_ private" (demangleSymbol mangled) "[init] Y.foo [private]"

-- ============================================================================
-- initialize_ prefixes
-- ============================================================================

#eval checkSome "initialize bare"
  (demangleSymbol "initialize_Init_Control_Basic") "[module_init] Init.Control.Basic"
#eval checkSome "initialize l_"
  (demangleSymbol "initialize_l_Lean_Meta_foo") "[module_init] Lean.Meta.foo"

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
  checkSome "lambda_2" (demangleSymbol (name.mangle "l_")) "foo [λ]"

#eval do
  let name := mkName [.inl "foo", .inl "_elam"]
  checkSome "elam" (demangleSymbol (name.mangle "l_")) "foo [λ]"

#eval do
  let name := mkName [.inl "foo", .inl "_jp"]
  checkSome "jp" (demangleSymbol (name.mangle "l_")) "foo [jp]"

#eval do
  let name := mkName [.inl "myConst", .inl "_closed", .inr 0]
  checkSome "closed" (demangleSymbol (name.mangle "l_")) "myConst [closed]"

#eval do
  let name := mkName [.inl "myConst", .inl "_closed_0"]
  checkSome "closed indexed" (demangleSymbol (name.mangle "l_")) "myConst [closed]"

#eval do
  let name := mkName [.inl "foo", .inl "_redArg", .inl "_boxed"]
  checkSome "multiple suffixes" (demangleSymbol (name.mangle "l_"))
    "foo [boxed, arity↓]"

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
  let name := mkName [.inl "f",
                       .inl "_at_", .inl "g", .inl "_spec", .inr 1,
                       .inl "_at_", .inl "h", .inl "_spec", .inr 2]
  checkSome "multiple at" (demangleSymbol (name.mangle "l_"))
    "f spec at g spec at h"

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

-- ============================================================================
-- Backtrace line parsing: macOS format
-- ============================================================================

#eval checkSome "bt macos"
  (demangleBtLine "3   lean   0x00000001001234 l_Lean_Meta_foo + 42")
  "3   lean   0x00000001001234 Lean.Meta.foo + 42"

-- ============================================================================
-- Backtrace line parsing: non-Lean lines unchanged
-- ============================================================================

#eval checkNone "bt non-lean"
  (demangleBtLine "./lean(printf+0x10) [0x7fff]")

-- ============================================================================
-- Edge cases: never crashes
-- ============================================================================

#eval do
  let inputs := #[
    "", "l_", "lp_", "lp_x", "_init_", "initialize_",
    "l_____", "lp____", "l_00", "l_0",
    "some random string", "l_ space"
  ]
  inputs.forM fun inp => do
    let _ := demangleSymbol inp
    let _ := demangleBtLine inp
    pure ()

-- ============================================================================
-- C export wrappers (test via getD "" since CStr functions are not public)
-- ============================================================================

#eval check "export symbol"
  ((demangleSymbol "l_Lean_Meta_foo").getD "") "Lean.Meta.foo"
#eval check "export symbol none"
  ((demangleSymbol "printf").getD "") ""
#eval check "export bt line"
  ((demangleBtLine "./lean(l_foo+0x1) [0x2]").getD "") "./lean(foo+0x1) [0x2]"
#eval check "export bt line none"
  ((demangleBtLine "no lean symbols here").getD "") ""

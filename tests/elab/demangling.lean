module
import Lean.Compiler.NameMangling
import Lean.Compiler.NameDemangling

/-!
# Tests for Lean Name Demangling

Tests the full demangling pipeline from `NameDemangling.lean`.
-/

open Lean.Name.Demangle
open Lean (Name)

/-!
Basic l_ prefix demangling
-/

#guard demangleSymbol "l_Lean_Meta_Sym_main" == "Lean.Meta.Sym.main"
#guard demangleSymbol "l_main" == "main"

/-!
lp_ prefix with package names
-/

#guard
  let mangled := Name.mangle `std.Lean.Meta.foo "lp_"
  demangleSymbol mangled == "Lean.Meta.foo (std)"

#guard
  let mangled := Name.mangle `my_pkg.Lean.Meta.foo "lp_"
  demangleSymbol mangled == "Lean.Meta.foo (my_pkg)"

#guard
  -- Package with escaped chars (hyphen → _x2d): split must not break mid-escape
  let mangled := Name.mangle `Lean.Meta.foo (s!"lp_{String.mangle "my-pkg"}_")
  demangleSymbol mangled == "Lean.Meta.foo (my-pkg)"

#guard
  let name := (`pkg._private.X).num 0 ++ `Y.foo
  let mangled := name.mangle "lp_"
  demangleSymbol mangled == "Y.foo [private] (pkg)"

/-!
_init_ prefixes
-/

#guard demangleSymbol "_init_l_Lean_Meta_foo" == "[init] Lean.Meta.foo"

#guard
  let name := (`_private.X).num 0 ++ `Y.foo
  let mangled := "_init_" ++ name.mangle "l_"
  demangleSymbol mangled == "[init] Y.foo [private]"

#guard
  let mangled := Name.mangle `std.Lean.Meta.foo "lp_"
  demangleSymbol ("_init_" ++ mangled) == "[init] Lean.Meta.foo (std)"

/-!
initialize_ prefixes
-/

#guard demangleSymbol "initialize_Init_Control_Basic" == "[module_init] Init.Control.Basic"

/-!
lean_apply_N and _lean_main
-/

#guard demangleSymbol "lean_apply_5" == "<apply/5>"
#guard demangleSymbol "lean_apply_12" == "<apply/12>"
#guard demangleSymbol "_lean_main" == "[lean] main"

/-!
.cold.N suffix handling
-/

#guard
  let mangled := Name.mangle `Lean.Meta.foo._redArg "l_"
  demangleSymbol (mangled ++ ".cold.1") == "Lean.Meta.foo [arity↓] .cold.1"

#guard demangleSymbol "l_Lean_Meta_foo.cold" == "Lean.Meta.foo .cold"

#guard demangleSymbol "lean_apply_5.cold.1" == "<apply/5> .cold.1"

#guard demangleSymbol "_lean_main.cold.1" == "[lean] main .cold.1"

/-!
Non-Lean symbols return none
-/

#guard demangleSymbol "printf" == none
#guard demangleSymbol "malloc" == none
#guard demangleSymbol "" == none

/-!
Postprocessing: suffix folding
-/

#guard
  let name := `foo._boxed
  demangleSymbol name.mangle == "foo [boxed]"

#guard
  let name := `foo._redArg
  demangleSymbol name.mangle == "foo [arity↓]"

#guard
  let name := `foo._impl
  demangleSymbol name.mangle == "foo [impl]"

#guard
  let name := `foo._override
  demangleSymbol name.mangle == "foo [override]"

#guard
  let name := `foo._lam_0
  demangleSymbol name.mangle == "foo [λ]"

#guard
  let name := `foo._elam_1
  demangleSymbol name.mangle == "foo [λ]"

#guard
  let name := `foo._closed_0
  demangleSymbol name.mangle == "foo [closed]"

#guard
  let name := `foo._redArg._boxed
  demangleSymbol name.mangle == "foo [boxed, arity↓]"

#guard
  -- _lam_0 followed by _boxed
  let name := `Lean.Meta.Simp.simpLambda._lam_0._boxed
  demangleSymbol name.mangle == "Lean.Meta.Simp.simpLambda [boxed, λ]"

#guard
  -- _redArg followed by _lam_0
  let name := `Lean.profileitIOUnsafe._redArg._lam_0
  demangleSymbol name.mangle == "Lean.profileitIOUnsafe [λ, arity↓]"

/-!
Postprocessing: private name stripping
-/

#guard
  let name := (`_private.Lean.Meta.Basic).num 0 ++ `Lean.Meta.foo
  demangleSymbol name.mangle == "Lean.Meta.foo [private]"

#guard
  let name := (`_private.Lean.Meta.Basic).num 0 ++ `Lean.Meta.foo._redArg
  demangleSymbol name.mangle == "Lean.Meta.foo [private, arity↓]"

/-!
Postprocessing: macro scopes stripping
-/

#guard
  let name := Lean.addMacroScope `Lean.Meta `Lean.Meta.foo 42
  demangleSymbol name.mangle == "Lean.Meta.foo"

#guard
  -- _boxed after macro scopes should still be recognized
  let name := (Lean.addMacroScope `Lean.Meta `Lean.Meta.foo 42).str "_boxed"
  demangleSymbol name.mangle == "Lean.Meta.foo [boxed]"

#guard
  -- _lam_0 before macro scopes and _boxed after should both be recognized
  let name := (Lean.addMacroScope `Lean.Elab `Lean.initFn._lam_0 42).str "_boxed"
  demangleSymbol name.mangle == "Lean.initFn [boxed, λ]"

/-!
Postprocessing: specialization contexts
-/

#guard
  let name := `List.map._at_.Foo.bar.spec_3
  demangleSymbol name.mangle == "List.map spec at Foo.bar"

#guard
  let name := `Lean.MVarId.withContext._at_.Foo.bar.spec_2._boxed
  demangleSymbol name.mangle == "Lean.MVarId.withContext spec at Foo.bar [boxed]"

#guard
  let name := `Lean.Meta.foo._at_.Lean.Meta.bar._elam_1._redArg.spec_2
  demangleSymbol name.mangle == "Lean.Meta.foo spec at Lean.Meta.bar [arity↓, λ]"

#guard
  -- Duplicate flag labels are deduplicated: _lam_0 + _elam_1 both map to λ
  let name := `f._at_.g._lam_0._elam_1._redArg.spec_1
  demangleSymbol name.mangle == "f spec at g [arity↓, λ]"

set_option trace.compiler.ir.result true in
def test (x : Nat) : StateM Nat Nat := do
  for i in *...x do
    for j in List.range i do
      modify fun x => x + j
  return 3

#eval
  let name := `f._at_.g.spec_1._at_.h.spec_2
  demangleSymbol name.mangle --== "f spec at g spec at h"

#guard
  -- Multiple spec at with flags on base and contexts
  let name := mkName [.inl "f",
                       .inl "_at_", .inl "g", .inl "_redArg", .inl "_spec", .inr 1,
                       .inl "_at_", .inl "h", .inl "_lam_0", .inl "_spec", .inr 2,
                       .inl "_boxed"]
  check "multiple at with flags" (demangleSymbol name.mangle)
    "f [boxed] spec at g[arity↓] spec at h[λ]"

#guard
  -- Base trailing suffix appearing after _spec N
  let name := mkName [.inl "f", .inl "_at_", .inl "g", .inl "_spec", .inr 1,
                       .inl "_lam_0"]
  check "base flags after spec" (demangleSymbol name.mangle)
    "f [λ] spec at g"

#guard
  -- spec_0 entries in context should be stripped
  let name := mkName [.inl "Lean", .inl "Meta", .inl "transformWithCache", .inl "visit",
                       .inl "_at_",
                       .inl "_private", .inl "Lean", .inl "Meta", .inl "Transform", .inr 0,
                       .inl "Lean", .inl "Meta", .inl "transform",
                       .inl "Lean", .inl "Meta", .inl "Sym", .inl "unfoldReducible",
                       .inl "spec_0", .inl "spec_0",
                       .inl "_spec", .inr 1]
  check "spec context strip spec_0" (demangleSymbol name.mangle)
    "Lean.Meta.transformWithCache.visit spec at Lean.Meta.transform.Lean.Meta.Sym.unfoldReducible"

#guard
  -- _private in spec context should be stripped
  let name := mkName [.inl "Array", .inl "mapMUnsafe", .inl "map",
                       .inl "_at_",
                       .inl "_private", .inl "Lean", .inl "Meta", .inl "Transform", .inr 0,
                       .inl "Lean", .inl "Meta", .inl "transformWithCache", .inl "visit",
                       .inl "_spec", .inr 1]
  check "spec context strip private" (demangleSymbol name.mangle)
    "Array.mapMUnsafe.map spec at Lean.Meta.transformWithCache.visit"

/-!
-- Complex real-world name
/-!

#guard
  let name := mkName [.inl "Lean", .inl "MVarId", .inl "withContext",
                       .inl "_at_",
                       .inl "_private", .inl "Lean", .inl "Meta", .inl "Sym", .inr 0,
                       .inl "Lean", .inl "Meta", .inl "Sym", .inl "BackwardRule", .inl "apply",
                       .inl "_spec", .inr 2,
                       .inl "_redArg", .inl "_lambda", .inr 0, .inl "_boxed"]
  check "complex" (demangleSymbol name.mangle)
    "Lean.MVarId.withContext [boxed, λ, arity↓] spec at Lean.Meta.Sym.BackwardRule.apply"

/-!
-- Backtrace line parsing: Linux glibc format
/-!

#eval check "bt linux"
  (demangleBtLine "./lean(l_Lean_Meta_foo+0x2a) [0x555555555555]")
  "./lean(Lean.Meta.foo+0x2a) [0x555555555555]"

#guard
  let name := mkName [.inl "foo", .inl "_boxed"]
  let sym := name.mangle "l_"
  check "bt linux boxed"
    (demangleBtLine s!"./lean({sym}+0x10) [0x7fff]")
    "./lean(foo [boxed]+0x10) [0x7fff]"

#guard
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "foo"]
  let sym := name.mangle "l_"
  check "bt linux private"
    (demangleBtLine s!"./lean({sym}+0x10) [0x7fff]")
    "./lean(Lean.Meta.foo [private]+0x10) [0x7fff]"

#guard
  let name := mkName [.inl "_private", .inl "Lean", .inl "Meta", .inl "Basic",
                       .inr 0, .inl "Lean", .inl "Meta", .inl "foo", .inl "_redArg"]
  let sym := name.mangle "l_"
  check "bt linux private + redArg"
    (demangleBtLine s!"./lean({sym}+0x10) [0x7fff]")
    "./lean(Lean.Meta.foo [arity↓, private]+0x10) [0x7fff]"

/-!
-- Backtrace line parsing: macOS format
/-!

#eval check "bt macos"
  (demangleBtLine "3   lean   0x00000001001234 l_Lean_Meta_foo + 42")
  "3   lean   0x00000001001234 Lean.Meta.foo + 42"

#guard
  let name := mkName [.inl "foo", .inl "_redArg"]
  let sym := name.mangle "l_"
  check "bt macos redArg"
    (demangleBtLine s!"3   lean   0x00000001001234 {sym} + 42")
    "3   lean   0x00000001001234 foo [arity↓] + 42"

/-!
-- Backtrace line parsing: non-Lean lines unchanged
/-!

#eval check "bt non-lean" none
  (demangleBtLine "./lean(printf+0x10) [0x7fff]")

#eval check "bt no parens" none
  (demangleBtLine "just some random text")

/-!
-- Edge cases: never crashes
/-!

#guard
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

/-!
-- C export wrappers
/-!

#eval check "export symbol"
  ((demangleSymbol "l_Lean_Meta_foo").getD "") "Lean.Meta.foo"
#eval check "export symbol none"
  ((demangleSymbol "printf").getD "") ""
#eval check "export bt line"
  ((demangleBtLine "./lean(l_foo+0x1) [0x2]").getD "") "./lean(foo+0x1) [0x2]"
#eval check "export bt line none"
  ((demangleBtLine "no lean symbols here").getD "") ""

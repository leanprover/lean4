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

#guard demangleSymbol "_init_lean_test_fn" == "[init] lean_test_fn"

/-!
initialize_ prefixes
-/

#guard demangleSymbol "initialize_Init_Control_Basic" == "[module_init] Init.Control.Basic"
#guard demangleSymbol "meta_initialize_Init_Control_Basic" == "[meta_module_init] Init.Control.Basic"
#guard demangleSymbol "runtime_initialize_Init_Control_Basic" == "[runtime_module_init] Init.Control.Basic"

#guard demangleSymbol "initialize__std_Init_Control_Basic" == "[module_init] Init.Control.Basic (std)"
#guard demangleSymbol "meta_initialize__std_Init_Control_Basic" == "[meta_module_init] Init.Control.Basic (std)"
#guard demangleSymbol "runtime_initialize__std_Init_Control_Basic" == "[runtime_module_init] Init.Control.Basic (std)"

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
  let name := `foo._elam_1._lam_0
  demangleSymbol name.mangle == "foo [λ]"

#guard
  let name := `foo._closed_0
  demangleSymbol name.mangle == "foo [closed]"

#guard
  let name := `foo._redArg._boxed
  demangleSymbol name.mangle == "foo [arity↓, boxed]"

#guard
  let name := `Lean.Meta.Simp.simpLambda._lam_0._boxed
  demangleSymbol name.mangle == "Lean.Meta.Simp.simpLambda [λ, boxed]"

#guard
  let name := `Lean.profileitIOUnsafe._redArg._lam_0
  demangleSymbol name.mangle == "Lean.profileitIOUnsafe [arity↓, λ]"

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
  demangleSymbol name.mangle == "Lean.initFn [λ, boxed]"

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
  demangleSymbol name.mangle == "Lean.Meta.foo spec at Lean.Meta.bar [λ, arity↓]"

#guard
  let name := `f._at_.g.spec_1._at_.h.spec_2
  demangleSymbol name.mangle == "f spec at g spec at h"

#guard
  -- Multiple spec at with flags on base and contexts
  let name := `f._at_.g._impl.spec_1._at_.h._elam_0.spec_2._redArg._boxed
  demangleSymbol name.mangle == "f spec at g [impl] spec at h [λ] [arity↓, boxed]"

#guard
  -- Base trailing suffix appearing after _spec N
  let name := `f._at_.g.spec_1._lam_0
  demangleSymbol name.mangle == "f spec at g [λ]"

#guard
  let name := (`_private.X).num 0 ++ `foo._at_.bar.spec_0
  demangleSymbol name.mangle == "foo [private] spec at bar" -- and not `foo spec at bar [private]`

#guard
  let name := Lean.addMacroScope `X `foo 3
    |>.appendCore `_at_
    |>.appendCore (Lean.addMacroScope `X `bar 3)
    |>.appendCore `spec_0
  demangleSymbol name.mangle == "foo spec at bar"

/-!
Complex real-world names
-/

#guard
  let name := (`_private.Lean.Meta.Transform).num 0 ++ `Lean.Meta.transformWithCache.visit._at_ ++
    `Lean.Meta.transform._at_.Lean.Meta.Sym.unfoldReducible.spec_0.spec_0
  demangleSymbol name.mangle ==
    "Lean.Meta.transformWithCache.visit [private] spec at Lean.Meta.transform spec at Lean.Meta.Sym.unfoldReducible"

#guard
  let name := `Lean.MVarId.withContext._at_.Lean.Meta.Sym.BackwardRule.apply.spec_2._redArg._lam_0._boxed
  demangleSymbol name.mangle ==
    "Lean.MVarId.withContext spec at Lean.Meta.Sym.BackwardRule.apply [arity↓, λ, boxed]"

/-!
Backtrace line parsing: Linux glibc format
-/

#guard
  demangleBtLine "./lean(l_Lean_Meta_foo+0x2a) [0x555555555555]" ==
    "./lean(Lean.Meta.foo+0x2a) [0x555555555555]"

#guard
  let name := `foo._boxed
  let sym := name.mangle
  demangleBtLine s!"./lean({sym}+0x10) [0x7fff]" == "./lean(foo [boxed]+0x10) [0x7fff]"

#guard
  let name := (`_private.Lean.Meta.Basic).num 0 ++ `Lean.Meta.foo
  let sym := name.mangle
  demangleBtLine s!"./lean({sym}+0x10) [0x7fff]" == "./lean(Lean.Meta.foo [private]+0x10) [0x7fff]"

#guard
  let name := (`_private.Lean.Meta.Basic).num 0 ++ `Lean.Meta.foo._redArg
  let sym := name.mangle
  demangleBtLine s!"./lean({sym}+0x10) [0x7fff]" ==
    "./lean(Lean.Meta.foo [private, arity↓]+0x10) [0x7fff]"

/-!
Backtrace line parsing: macOS format
-/

#guard demangleBtLine "3   lean   0x00000001001234 l_Lean_Meta_foo + 42" ==
  "3   lean   0x00000001001234 Lean.Meta.foo + 42"

#guard
  let name := `foo._redArg
  let sym := name.mangle
  demangleBtLine s!"3   lean   0x00000001001234 {sym} + 42" ==
    "3   lean   0x00000001001234 foo [arity↓] + 42"

/-!
Backtrace line parsing: non-Lean lines unchanged
-/

#guard demangleBtLine "./lean(printf+0x10) [0x7fff]" == none
#guard demangleBtLine "just some random text" == none

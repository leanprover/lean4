module

import Module.Basic

/-! `private import` should allow only private access to imported decls. -/

public def g := f

/--
error: Unknown identifier `f`

Note: A public declaration `f` exists but is imported privately; consider adding `public import Module.Basic`.
-/
#guard_msgs in
public theorem t2 : f = 1 := sorry

/--
error: Unknown identifier `f`

Note: A public declaration `f` exists but is imported privately; consider adding `public import Module.Basic`.
-/
#guard_msgs in
@[expose] public def h : True := f

/-! `initialize` should be run even if imported IR-only. -/

public def publicDefOfPrivatelyInitialized := initialized

/-! #12198: `local simp` should be accepted on privately imported theorem -/

attribute [local simp] t

/-- Setup for #12833. -/
public def Namespaced.def2 := 0

/-! Default instances from privately imported modules must not be applied during
public-scope elaboration. Without the visibility filter on default instances, the
priv-imported `instHMulNatCustom` would be tried before the core `instHMul` and
fail with `Unknown constant` in this public theorem signature. -/

public theorem hmulDefaultPrivacy (m : Nat) : ∀ n, m * n = m * n := by
  intro n
  rfl

public structure StructWithPrivImportedFieldType where
  private field : UInt8Struct
deriving Inhabited

/-!
Construct and extract values of a public type whose only field's type is privately imported.
The defining module is the only place that sees the private field type, so trivial structure
optimizations (eliding constructor, unboxing type) should be disabled.
-/

/--
trace: [Compiler.result] size: 2
    def mkSwpift n : obj :=
      let _x.1 := ctor_0.0.1[_private.Module.PrivateImported.0.StructWithPrivImportedFieldType.mk];
      sset _x.1[0, 0] := n;
      return _x.1
[Compiler.result] size: 2
    def mkSwpift._boxed n : obj :=
      let n.boxed := unbox n;
      let res := mkSwpift n.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
public def mkSwpift (n : UInt8) : StructWithPrivImportedFieldType := ⟨⟨n⟩⟩

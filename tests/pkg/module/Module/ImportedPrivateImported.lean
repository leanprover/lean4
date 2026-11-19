module

prelude
public import Module.PrivateImported

/-! `private import` should not be transitive. -/

/-- error: Unknown identifier `f` -/
#guard_msgs in
#check f

/-- info: 5 -/
#guard_msgs in
#eval publicDefOfPrivatelyInitialized

/-! #12833: namespaces privately imported but publicly used must be re-exported. -/
open Namespaced

/-! Re-check `mkSwpift` invariants. -/

/--
trace: [Compiler.result] size: 1
    def _private.Module.ImportedPrivateImported.0.mkSwpift2 n : obj :=
      let _x.1 := mkSwpift n;
      return _x.1
[Compiler.result] size: 2
    def _private.Module.ImportedPrivateImported.0.mkSwpift2._boxed n : obj :=
      let n.boxed := unbox n;
      let res := _private.Module.ImportedPrivateImported.0.mkSwpift2 n.boxed;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def mkSwpift2 (n : UInt8) : StructWithPrivImportedFieldType := mkSwpift n

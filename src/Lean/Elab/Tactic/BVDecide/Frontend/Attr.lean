/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Henrik Böving
-/
prelude
import Lean.Util.Trace
import Lean.Elab.Tactic.Simp
import Std.Tactic.BVDecide.Syntax

/-!
Provides environment extensions around the `bv_decide` tactic frontends.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Lean
open Lean.Meta.Simp

builtin_initialize registerTraceClass `Meta.Tactic.sat
builtin_initialize registerTraceClass `Meta.Tactic.bv

register_builtin_option sat.solver : String := {
  defValue := ""
  descr :=
    "Name of the SAT solver used by Lean.Elab.Tactic.BVDecide tactics.\n
     1. If this is set to something besides the empty string they will use that binary.\n
     2. If this is set to the empty string they will check if there is a cadical binary next to the\
        executing program. Usually that program is going to be `lean` itself and we do ship a\
        `cadical` next to it.\n
     3. If that does not succeed try to call `cadical` from PATH. The empty string default indicates\
        to use the one that ships with Lean."
}

declare_config_elab elabBVDecideConfig Lean.Elab.Tactic.BVDecide.Frontend.BVDecideConfig

builtin_initialize bvNormalizeExt : Meta.SimpExtension ←
  Meta.registerSimpAttr `bv_normalize "simp theorems used by bv_normalize"

/-- Builtin `bv_normalize` simprocs. -/
builtin_initialize builtinBVNormalizeSimprocsRef : IO.Ref Meta.Simp.Simprocs ← IO.mkRef {}

builtin_initialize bvNormalizeSimprocExt : Meta.Simp.SimprocExtension ←
  Meta.Simp.registerSimprocAttr `bv_normalize_proc "simprocs used by bv_normalize" (some builtinBVNormalizeSimprocsRef)

private def addBuiltin (declName : Name) (stx : Syntax) (addDeclName : Name) : AttrM Unit := do
  let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
  let procExpr ← match (← getConstInfo declName).type with
    | .const ``Simproc _  => pure <| mkApp3 (mkConst ``Sum.inl [0, 0]) (mkConst ``Simproc) (mkConst ``DSimproc) (mkConst declName)
    | _ => throwError "unexpected type at bv_normalize simproc"
  let val := mkAppN (mkConst addDeclName) #[toExpr declName, toExpr post, procExpr]
  let initDeclName ← mkFreshUserName (declName ++ `declare)
  declareBuiltin initDeclName val

def addBVNormalizeProcBuiltinAttr (declName : Name) (post : Bool) (proc : Sum Simproc DSimproc) : IO Unit :=
  addSimprocBuiltinAttrCore builtinBVNormalizeSimprocsRef declName post proc

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `bvNormalizeProcBuiltinAttr
    descr           := "Builtin bv_normalize simproc"
    applicationTime := AttributeApplicationTime.afterCompilation
    erase           := fun _ => throwError "Not implemented yet, [-builtin_bv_normalize_proc]"
    add             := fun declName stx _ => addBuiltin declName stx ``addBVNormalizeProcBuiltinAttr
  }

end Frontend
namespace Lean.Elab.Tactic.BVDecide

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ReplaceExpr
import Lean.Compiler.ImplementedByAttr
import Lean.Meta.AppBuilder
import Lean.Meta.Basic

namespace Lean
namespace Meta

private def mkUnsafeNameFor (n : Name) := n ++ `_unsafe

private def addUnsafeDecls (ds : List DefinitionVal) : MetaM Unit := do
let ds := ds.map fun d =>
  { d with
    name  := mkUnsafeNameFor d.name,
    value := d.value.replace fun e => match e with
      | Expr.const constName us _ =>
        if ds.any fun d => d.name == constName then
          some $ mkConst (mkUnsafeNameFor constName) us
        else
          none
      | _ => none };
addAndCompile (Declaration.mutualDefnDecl ds)

private def mkInhabitant? (type : Expr) : MetaM (Option Expr) :=
catch
  (do inh ← mkAppM `arbitrary #[type]; pure inh)
  (fun _ => pure none)

private def findAssumption? (xs : Array Expr) (type : Expr) : MetaM (Option Expr) := do
xs.findM? fun x => do {
  xType ← inferType x;
  isDefEq xType type
}

private def mkFnInhabitantAux? (xs : Array Expr) : Nat → Expr → MetaM (Option Expr)
| 0,   type => mkInhabitant? type
| i+1, type => do
  let x := xs.get! i;
  type ← mkForallFVars #[x] type;
  val? ← mkInhabitant? type;
  match val? with
  | none     => mkFnInhabitantAux? i type
  | some val => do
    val ← mkLambdaFVars (xs.extract 0 i) val;
    pure $ some val

private def mkFnInhabitant? (xs : Array Expr) (type : Expr) : MetaM (Option Expr) :=
mkFnInhabitantAux? xs xs.size type

private def mkInhabitantFor (declName : Name) (xs : Array Expr) (type : Expr) : MetaM Expr := do
val? ← mkInhabitant? type;
match val? with
| some val => mkLambdaFVars xs val
| none     => do
x? ← findAssumption? xs type;
match x? with
| some x => mkLambdaFVars xs x
| none   => do
val? ← mkFnInhabitant? xs type;
match x? with
| some val => pure val
| none => throwError ("failed to compile partial definition '" ++ declName ++ "', failed to show that type is inhabited")

private def addOpaqueConstants (ds : List DefinitionVal) : MetaM Unit := do
ds.forM fun d =>
  forallTelescopeReducing d.type fun xs type => do
    inh ← mkInhabitantFor d.name xs type;
    addAndCompile $ Declaration.opaqueDecl { name := d.name, lparams := d.lparams, type := d.type, value := inh, isUnsafe := false };
    setImplementedBy d.name (mkUnsafeNameFor d.name)

def addPartialDecls (ds : List DefinitionVal) : MetaM Unit := do
addUnsafeDecls ds;
addOpaqueConstants ds

end Meta
end Lean

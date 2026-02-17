/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Init.CbvSimproc
public import Lean.Meta.Tactic.Cbv.CbvSimprocExt
public import Lean.Elab.Command

public section

namespace Lean.Elab
open Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym
open Lean.Meta.Sym.Simp
open Lean.Meta.DiscrTree

/-- Elaborate a cbv simproc pattern term into an `Expr` (with metavariables for wildcards). -/
def elabCbvSimprocPattern (stx : Syntax) : MetaM Expr := do
  let go : TermElabM Expr := do
    let pattern ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars
    return pattern
  go.run'

/-- Elaborate a pattern and convert to Sym discrimination tree keys. -/
def elabCbvSimprocKeys (stx : Syntax) : MetaM (Array Key) := do
  let pattern ← elabCbvSimprocPattern stx
  let symPattern ← mkSimprocPatternFromExpr pattern
  return symPattern.mkDiscrTreeKeys

def checkCbvSimprocType (declName : Name) : CoreM Unit := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``Lean.Meta.Sym.Simp.Simproc _ => pure ()
  | _ => throwError "Expected `{.ofConstName ``Lean.Meta.Sym.Simp.Simproc}`, but `{declName}` has type{indentExpr decl.type}"

namespace Command

@[builtin_command_elab Lean.Parser.cbvSimprocPattern] def elabCbvSimprocPattern : CommandElab := fun stx => do
  let `(cbv_simproc_pattern% $postOrPre $pattern => $declName) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload declName
    checkCbvSimprocType declName
    let keys ← elabCbvSimprocKeys pattern
    let post := postOrPre.raw.getKind == `token.post
    cbvSimprocExt.add { declName, post, keys } .global

@[builtin_command_elab Lean.Parser.cbvSimprocPatternBuiltin] def elabCbvSimprocPatternBuiltin : CommandElab := fun stx => do
  let `(builtin_cbv_simproc_pattern% $postOrPre $pattern => $declName) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload declName
    checkCbvSimprocType declName
    let keys ← elabCbvSimprocKeys pattern
    let post := postOrPre.raw.getKind == `token.post
    let val := mkAppN (mkConst ``registerBuiltinCbvSimproc) #[toExpr declName, toExpr post, toExpr keys, mkConst declName]
    let initDeclName ← mkFreshUserName (declName ++ `declare)
    declareBuiltin initDeclName val

end Command

private def isPostFromAttrStx (stx : Syntax) : Bool :=
  if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost

builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvSimprocAttrRef
    name  := `cbvSimprocAttr
    descr := "Register a simproc for `cbv` evaluation."
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName stx kind => do
      let post := isPostFromAttrStx stx
      let (_, _) ← Lean.Meta.MetaM.run (do
        checkCbvSimprocType declName
        let (_, keys) ← do
          let builtinDecls ← builtinCbvSimprocDeclsRef.get
          if let some entry := builtinDecls[declName]? then
            pure entry
          else
            throwError "Invalid `[cbv_simproc]` attribute: `{.ofConstName declName}` has no registered pattern. Use `cbv_simproc_decl` to declare it."
        let proc ← getCbvSimprocFromDecl declName
        cbvSimprocExt.add { declName, post, keys } kind
        builtinCbvSimprocsRef.modify fun s => s.insert post keys { declName, proc }
      ) {}
  }

builtin_initialize
  registerBuiltinAttribute {
    ref   := `cbvSimprocBuiltinAttrRef
    name  := `cbvSimprocBuiltinAttr
    descr := "Register a builtin simproc for `cbv` evaluation."
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName stx _ => do
      let post := isPostFromAttrStx stx
      let (_, _) ← (do
        checkCbvSimprocType declName
        let some (_, keys) := (← builtinCbvSimprocDeclsRef.get)[declName]?
          | throwError "Invalid `[builtin_cbv_simproc]` attribute: `{.ofConstName declName}` is not a builtin cbv simproc"
        let proc ← getCbvSimprocFromDecl declName
        builtinCbvSimprocsRef.modify fun s => s.insert post keys { declName, proc }
        : Lean.Meta.MetaM Unit).run {}
  }

end Lean.Elab

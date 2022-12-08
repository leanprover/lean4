/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

/-- Helper class for lifting `CompilerM.codeBind` -/
class MonadCodeBind (m : Type → Type) where
  codeBind : (c : Code) → (f : FVarId → m Code) → m Code

/--
Return code that is equivalent to `c >>= f`. That is, executes `c`, and then `f x`, where
`x` is a variable that contains the result of `c`'s computation.

If `c` contains a jump to a join point `jp_i` not declared in `c`, we throw an exception because
an invalid block would be generated. It would be invalid because `f` would not
be applied to `jp_i`. Note that, we could have decided to create a copy of `jp_i` where we apply `f` to it,
by we decided to not do it to avoid code duplication.
-/
abbrev Code.bind [MonadCodeBind m] (c : Code) (f : FVarId → m Code) : m Code :=
  MonadCodeBind.codeBind c f

partial def CompilerM.codeBind (c : Code) (f : FVarId → CompilerM Code) : CompilerM Code := do
  go c |>.run {}
where
  go (c : Code) : ReaderT FVarIdSet CompilerM Code := do
    match c with
    | .let decl k => return .let decl (← go k)
    | .fun decl k => return .fun decl (← go k)
    | .jp decl k =>
      let value ← go decl.value
      let type ← value.inferParamType decl.params
      let decl ← decl.update' type value
      withReader (fun s => s.insert decl.fvarId) do
        return .jp decl (← go k)
    | .cases c =>
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName params (← go k)
        | .default k => return .default (← go k)
      if alts.isEmpty then
        throwError "`Code.bind` failed, empty `cases` found"
      let resultType ← mkCasesResultType alts
      return .cases { c with alts, resultType }
    | .return fvarId => f fvarId
    | .jmp fvarId .. =>
      unless (← read).contains fvarId do
        throwError "`Code.bind` failed, it contains a out of scope join point"
      return c
    | .unreach type =>
      /-
      Create an auxiliary parameter `aux : type` to compute the resulting type of `f aux`.
      This code is not very efficient, we could ask caller to provide the type of `c >>= f`,
      but this is more convenient, and this case is seldom reached.
      -/
      let auxParam ← mkAuxParam type
      let k ← f auxParam.fvarId
      let typeNew ← k.inferType
      eraseCode k
      eraseParam auxParam
      return .unreach typeNew

instance : MonadCodeBind CompilerM where
  codeBind := CompilerM.codeBind

instance [MonadCodeBind m] : MonadCodeBind (ReaderT ρ m) where
  codeBind c f ctx := c.bind fun fvarId => f fvarId ctx

instance [STWorld ω m] [MonadCodeBind m] : MonadCodeBind (StateRefT' ω σ m) where
  codeBind c f sref := c.bind fun fvarId => f fvarId sref

/--
Create new parameters for the given arrow type.
Example: if `type` is `Nat → Bool → Int`, the result is
an array containing two new parameters with types `Nat` and `Bool`.
-/
partial def mkNewParams (type : Expr) : CompilerM (Array Param) :=
  go type #[] #[]
where
  go (type : Expr) (xs : Array Expr) (ps : Array Param) : CompilerM (Array Param) := do
    match type with
    | .forallE _ d b _ =>
      let d := d.instantiateRev xs
      let p ← mkAuxParam d
      go b (xs.push (.fvar p.fvarId)) (ps.push p)
    | _ =>
      let type := type.instantiateRev xs
      let type' := type.headBeta
      if type' != type then
        go type' #[] ps
      else
        return ps

def isEtaExpandCandidateCore (type : Expr) (params : Array Param) : Bool :=
  let typeArity := getArrowArity type
  let valueArity := params.size
  typeArity > valueArity

abbrev FunDeclCore.isEtaExpandCandidate (decl : FunDecl) : Bool :=
  isEtaExpandCandidateCore decl.type decl.params

def etaExpandCore (type : Expr) (params : Array Param) (value : Code) : CompilerM (Array Param × Code) := do
  let valueType ← instantiateForall type (params.map (mkFVar ·.fvarId))
  let psNew ← mkNewParams valueType
  let params := params ++ psNew
  let xs := psNew.map fun p => .fvar p.fvarId
  let value ← value.bind fun fvarId => do
    let auxDecl ← mkAuxLetDecl (.fvar fvarId xs)
    return .let auxDecl (.return auxDecl.fvarId)
  return (params, value)

def etaExpandCore? (type : Expr) (params : Array Param) (value : Code) : CompilerM (Option (Array Param × Code)) := do
  if isEtaExpandCandidateCore type params then
    etaExpandCore type params value
  else
    return none

def FunDeclCore.etaExpand (decl : FunDecl) : CompilerM FunDecl := do
  let some (params, value) ← etaExpandCore? decl.type decl.params decl.value | return decl
  decl.update decl.type params value

def Decl.etaExpand (decl : Decl) : CompilerM Decl := do
  let some (params, value) ← etaExpandCore? decl.type decl.params decl.value | return decl
  return { decl with params, value }

end Lean.Compiler.LCNF

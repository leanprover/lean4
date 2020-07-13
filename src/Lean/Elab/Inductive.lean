/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.Definition

namespace Lean
namespace Elab
namespace Command

structure CtorView :=
(ref       : Syntax)
(modifiers : Modifiers)
(inferMod  : Bool)  -- true if `{}` is used in the constructor declaration
(declName  : Name)
(binders   : Syntax)
(type?     : Option Syntax)

instance CtorView.inhabited : Inhabited CtorView :=
⟨{ ref := arbitrary _, modifiers := {}, inferMod := false, declName := arbitrary _, binders := arbitrary _, type? := none }⟩

structure InductiveView :=
(ref           : Syntax)
(modifiers     : Modifiers)
(shortDeclName : Name)
(declName      : Name)
(levelNames    : List Name)
(binders       : Syntax)
(type?         : Option Syntax)
(ctors         : Array CtorView)

instance InductiveView.inhabited : Inhabited InductiveView :=
⟨{ ref := arbitrary _, modifiers := {}, shortDeclName := arbitrary _, declName := arbitrary _,
   levelNames := [], binders := arbitrary _, type? := none, ctors := #[] }⟩

structure ElabHeaderResult :=
(view       : InductiveView)
(lctx       : LocalContext)
(localInsts : LocalInstances)
(params     : Array Expr)
(type       : Expr)

instance ElabHeaderResult.inhabited : Inhabited ElabHeaderResult :=
⟨{ view := arbitrary _, lctx := arbitrary _, localInsts := arbitrary _, params := #[], type := arbitrary _ }⟩

private partial def elabHeaderAux (views : Array InductiveView)
    : Nat → Array ElabHeaderResult → TermElabM (Array ElabHeaderResult)
| i, acc =>
  if h : i < views.size then
    let view := views.get ⟨i, h⟩;
    Term.elabBinders view.binders.getArgs fun params => do
      lctx ← Term.getLCtx;
      localInsts ← Term.getLocalInsts;
      match view.type? with
      | none         => do
        u ← Term.mkFreshLevelMVar view.ref;
        let type := mkSort (mkLevelSucc u);
        elabHeaderAux (i+1) (acc.push { lctx := lctx, localInsts := localInsts, params := params, type := type, view := view })
      | some typeStx => do
        type ← Term.elabTerm typeStx none;
        unlessM (Term.isTypeFormerType view.ref type) $
          Term.throwError typeStx "invalid inductive type, resultant type is not a sort";
        elabHeaderAux (i+1) (acc.push { lctx := lctx, localInsts := localInsts, params := params, type := type, view := view })
  else
    pure acc

private def checkNumParams (rs : Array ElabHeaderResult) : TermElabM Nat := do
let numParams := (rs.get! 0).params.size;
rs.forM fun r => unless (r.params.size == numParams) $
  Term.throwError r.view.ref "invalid inductive type, number of parameters mismatch in mutually inductive datatypes";
pure numParams

private def checkUnsafe (rs : Array ElabHeaderResult) : TermElabM Unit :=
let isUnsafe := (rs.get! 0).view.modifiers.isUnsafe;
rs.forM fun r => unless (r.view.modifiers.isUnsafe == isUnsafe) $
  Term.throwError r.view.ref "invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes"

private def checkLevelNames (rs : Array ElabHeaderResult) : TermElabM Unit := do
let levelNames := (rs.get! 0).view.levelNames;
rs.forM fun r => unless (r.view.levelNames == levelNames) $
  Term.throwError r.view.ref "invalid inductive type, universe parameters mismatch in mutually inductive datatypes"

private def mkTypeFor (r : ElabHeaderResult) : TermElabM Expr := do
Term.withLocalContext r.lctx r.localInsts do
  Term.mkForall r.view.ref r.params r.type

private def throwUnexpectedInductiveType {α} (ref : Syntax) : TermElabM α :=
Term.throwError ref "unexpected inductive resulting type"

-- Given `e` of the form `forall As, B`, return `B`.
private def getResultingType (ref : Syntax) (e : Expr) : TermElabM Expr :=
Term.liftMetaM ref $ Meta.forallTelescopeReducing e fun _ r => pure r

-- Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
private partial def checkParamsAndResultType (ref : Syntax) (numParams : Nat) : Nat → Expr → Expr → TermElabM Unit
| i, type, firstType => do
  type ← Term.whnf ref type;
  if i < numParams then do
    firstType ← Term.whnf ref firstType;
    match type, firstType with
    | Expr.forallE n₁ d₁ b₁ c₁, Expr.forallE n₂ d₂ b₂ c₂ => do
      unless (n₁ == n₂) $
        let msg : MessageData :=
          "invalid mutually inductive types, parameter name mismatch '" ++ n₁ ++ "', expected '" ++ n₂ ++ "'";
        Term.throwError ref msg;
      unlessM (Term.isDefEq ref d₁ d₂) $
        let msg : MessageData :=
          "invalid mutually inductive types, type mismatch at parameter '" ++ n₁ ++ "'" ++ indentExpr d₁
          ++ Format.line ++ "expected type" ++ indentExpr d₂;
        Term.throwError ref msg;
      unless (c₁.binderInfo == c₂.binderInfo) $
        -- TODO: improve this error message?
        Term.throwError ref ("invalid mutually inductive types, binder annotation mismatch at parameter '" ++ n₁ ++ "'");
      Term.withLocalDecl ref n₁ c₁.binderInfo d₁ fun x =>
        let type      := b₁.instantiate1 x;
        let firstType := b₂.instantiate1 x;
        checkParamsAndResultType (i+1) type firstType
    | _, _ => throwUnexpectedInductiveType ref
  else
    match type with
    | Expr.forallE n d b c =>
      Term.withLocalDecl ref n c.binderInfo d fun x =>
        let type      := b.instantiate1 x;
        checkParamsAndResultType (i+1) type firstType
    | Expr.sort _ _        => do
      firstType ← getResultingType ref firstType;
      unlessM (Term.isDefEq ref type firstType) $
        let msg : MessageData :=
          "invalid mutually inductive types, resulting universe mismatch, given " ++ indentExpr type ++ Format.line ++ "expected type" ++ indentExpr firstType;
        Term.throwError ref msg
    | _ => throwUnexpectedInductiveType ref

-- Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
private def checkHeader (r : ElabHeaderResult) (numParams : Nat) (firstType? : Option Expr) : TermElabM Expr := do
type ← mkTypeFor r;
match firstType? with
| none           => pure type
| some firstType => do
  checkParamsAndResultType r.view.ref numParams 0 type firstType;
  pure firstType

-- Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
private partial def checkHeaders (rs : Array ElabHeaderResult) (numParams : Nat) : Nat → Option Expr → TermElabM Unit
| i, firstType? => when (i < rs.size) do
  type ← checkHeader (rs.get! i) numParams firstType?;
  checkHeaders (i+1) type

private def elabHeader (views : Array InductiveView) : TermElabM (Array ElabHeaderResult) := do
rs ← elabHeaderAux views 0 #[];
when (rs.size > 1) do {
  checkUnsafe rs;
  checkLevelNames rs;
  numParams ← checkNumParams rs;
  checkHeaders rs numParams 0 none
};
pure rs

private partial def withInductiveLocalDeclsAux {α} (ref : Syntax) (namesAndTypes : Array (Name × Expr)) (params : Array Expr)
    (x : Array Expr → Array Expr → TermElabM α) : Nat → Array Expr → TermElabM α
| i, indFVars =>
  if h : i < namesAndTypes.size then do
    let (id, type) := namesAndTypes.get ⟨i, h⟩;
    type ← Term.liftMetaM ref (Meta.instantiateForall type params);
    Term.withLocalDecl ref id BinderInfo.default type fun indFVar => withInductiveLocalDeclsAux (i+1) (indFVars.push indFVar)
  else
    x params indFVars

/- Create a local declaration for each inductive type in `rs`, and execute `x params indFVars`, where `params` are the inductive type parameters and
   `indFVars` are the new local declarations.
   We use the the local context/instances and parameters of rs[0].
   Note that this method is executed after we executed `checkHeaders` and established all
   parameters are compatible. -/
private def withInductiveLocalDecls {α} (rs : Array ElabHeaderResult) (x : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
namesAndTypes ← rs.mapM fun r => do {
  type ← mkTypeFor r;
  -- _root_.dbgTrace (">>> " ++ toString r.view.shortDeclName ++ " : " ++ toString type) fun _ =>
  pure (r.view.shortDeclName, type)
};
let r0     := rs.get! 0;
let params := r0.params;
Term.withLocalContext r0.lctx r0.localInsts $
  withInductiveLocalDeclsAux r0.view.ref namesAndTypes params x 0 #[]

private def isInductiveFamily (ref : Syntax) (indFVar : Expr) : TermElabM Bool := do
indFVarType ← Term.inferType ref indFVar;
indFVarType ← Term.whnf ref indFVarType;
pure !indFVarType.isSort

/-
A `ctor` has the form
  parser! " | " >> ident >> optional inferMod >> optDeclSig -/
private def elabCtors (indFVar : Expr) (params : Array Expr) (r : ElabHeaderResult) : TermElabM (List Constructor) := do
let ref := r.view.ref;
indFamily ← isInductiveFamily ref indFVar;
r.view.ctors.toList.mapM fun ctorView => Term.elabBinders ctorView.binders.getArgs fun ctorParams => do
  let ref := ctorView.ref;
  type ← match ctorView.type? with
    | none          => do
      when indFamily $
        Term.throwError ref "constructor resulting type must be specified in inductive family declaration";
      pure indFVar
    | some ctorType => do {
      type ← Term.elabTerm ctorType none;
      resultingType ← getResultingType ref type;
      unless (resultingType.getAppFn == indFVar) $
        Term.throwError ref ("unexpected constructor resulting type" ++ indentExpr resultingType);
      unlessM (Term.isType ref resultingType) $
        Term.throwError ref ("unexpected constructor resulting type, type expected" ++ indentExpr resultingType);
      pure type
    };
  type ← Term.mkForall ref ctorParams type;
  type ← Term.mkForall ref params type;
  -- _root_.dbgTrace (">> " ++ toString ctorView.declName ++ " : " ++ toString type) fun _ =>
  pure { name := ctorView.declName, type := type }

private def mkInductiveDecl (views : Array InductiveView) : TermElabM Declaration := do
rs ← elabHeader views;
let view0      := views.get! 0;
let levelNames := view0.levelNames;
let isUnsafe   := view0.modifiers.isUnsafe;
withInductiveLocalDecls rs fun params indFVars => do
  indTypes ← views.size.foldM
    (fun i (indTypes : List InductiveType) => do
      let indFVar := indFVars.get! i;
      let r       := rs.get! i;
      ctors ← elabCtors indFVar params r;
      let indType := { name := r.view.declName, type := r.type, ctors := ctors : InductiveType };
      pure (indType :: indTypes))
    [];
  let indTypes := indTypes.reverse;
  let decl := Declaration.inductDecl levelNames params.size indTypes isUnsafe;
  -- TODO: compute resultant universe level
  -- TODO: convert local indFVars into constants
  -- TODO: use inferImplicit at ctors
  -- TODO: eliminate unused variables from params
  pure decl

def elabInductiveCore (views : Array InductiveView) : CommandElabM Unit := do
decl ← liftTermElabM none $ mkInductiveDecl views;
-- TODO
pure ()

end Command
end Elab
end Lean

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term

namespace Lean
namespace Elab
namespace Term
/--
  Given syntax of the forms
    a) (`:` term)?
    b) `:` term
  into `term` if it is present, or a hole if not. -/
private def expandBinderType (stx : Syntax) : Syntax :=
if stx.getNumArgs == 0 then
  mkHole
else
  stx.getArg 1

/-- Given syntax of the form `ident <|> hole`, return `ident`. If `hole`, then we create a new anonymous name. -/
private def expandBinderIdent (stx : Syntax) : TermElabM Syntax :=
if stx.getKind == `Lean.Parser.Term.hole then do
  mkFreshAnonymousIdent stx
else
  pure stx

/-- Given syntax of the form `(ident >> " : ")?`, return `ident`, or a new instance name. -/
private def expandOptIdent (stx : Syntax) : TermElabM Syntax :=
if stx.getNumArgs == 0 then do
  id ← mkFreshInstanceName; pure $ mkIdentFrom stx id
else
  pure $ stx.getArg 0

structure BinderView :=
(id : Syntax) (type : Syntax) (bi : BinderInfo)

private def matchBinder (stx : Syntax) : TermElabM (Array BinderView) :=
withNode stx $ fun node => do
  let k := node.getKind;
  if k == `Lean.Parser.Term.simpleBinder then
    -- binderIdent+
    let ids  := (node.getArg 0).getArgs;
    let type := mkHole;
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.explicitBinder then
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    let ids  := (node.getArg 1).getArgs;
    let type := expandBinderType (node.getArg 2);
    -- TODO handle `binderDefault` and `binderTactic`
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.implicitBinder then
    -- `{` binderIdent+ binderType `}`
    let ids  := (node.getArg 1).getArgs;
    let type := expandBinderType (node.getArg 2);
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.implicit }
  else if k == `Lean.Parser.Term.instBinder then do
    -- `[` optIdent type `]`
    id ← expandOptIdent (node.getArg 1);
    let type := node.getArg 2;
    pure #[ { id := id, type := type, bi := BinderInfo.instImplicit } ]
  else
    throwError stx "term elaborator failed, unexpected binder syntax"

private partial def elabBinderViews (binderViews : Array BinderView)
    : Nat → Array Expr → LocalContext → LocalInstances → TermElabM (Array Expr × LocalContext × LocalInstances)
| i, fvars, lctx, localInsts =>
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩;
    withLCtx lctx localInsts $ do
      type       ← elabType binderView.type;
      fvarId     ← mkFreshId;
      let fvar  := mkFVar fvarId;
      let fvars := fvars.push fvar;
      -- dbgTrace (toString binderView.id.getId ++ " : " ++ toString type);
      let lctx  := lctx.mkLocalDecl fvarId binderView.id.getId type binderView.bi;
      className? ← isClass binderView.type type;
      match className? with
      | none           => elabBinderViews (i+1) fvars lctx localInsts
      | some className => do
        resetSynthInstanceCache;
        let localInsts := localInsts.push { className := className, fvar := mkFVar fvarId };
        elabBinderViews (i+1) fvars lctx localInsts
  else
    pure (fvars, lctx, localInsts)

private partial def elabBindersAux (binders : Array Syntax)
    : Nat → Array Expr → LocalContext → LocalInstances → TermElabM (Array Expr × LocalContext × LocalInstances)
| i, fvars, lctx, localInsts =>
  if h : i < binders.size then do
    binderViews ← matchBinder (binders.get ⟨i, h⟩);
    (fvars, lctx, localInsts) ← elabBinderViews binderViews 0 fvars lctx localInsts;
    elabBindersAux (i+1) fvars lctx localInsts
  else
    pure (fvars, lctx, localInsts)

/--
  Elaborate the given binders (i.e., `Syntax` objects for `simpleBinder <|> bracktedBinder`),
  update the local context, set of local instances, reset instance chache (if needed), and then
  execute `x` with the updated context. -/
def elabBinders {α} (binders : Array Syntax) (x : Array Expr → TermElabM α) : TermElabM α :=
if binders.isEmpty then x #[]
else do
  lctx ← getLCtx;
  localInsts ← getLocalInsts;
  (fvars, lctx, newLocalInsts) ← elabBindersAux binders 0 #[] lctx localInsts;
  resettingSynthInstanceCacheWhen (newLocalInsts.size > localInsts.size) $
    adaptReader (fun (ctx : Context) => { lctx := lctx, localInstances := newLocalInsts, .. ctx }) (x fvars)

@[inline] def elabBinder {α} (binder : Syntax) (x : Expr → TermElabM α) : TermElabM α :=
elabBinders #[binder] (fun fvars => x (fvars.get! 1))

@[builtinTermElab «forall»] def elabForall : TermElab :=
fun stx _ =>
  -- `forall` binders+ `,` term
  let binders := (stx.getArg 1).getArgs;
  let term    := stx.getArg 3;
  elabBinders binders $ fun xs => do
    e ← elabType term;
    mkForall stx.val xs e

@[builtinTermElab arrow] def elabArrow : TermElab :=
fun stx expectedType? => do
  id ← mkFreshAnonymousIdent stx.val;
  let dom    := stx.getArg 0;
  let rng    := stx.getArg 2;
  let newStx := mkNode `Lean.Parser.Term.forall #[mkAtom "forall", mkNullNode #[mkExplicitBinder id dom], mkAtom ",", rng];
  elabTerm newStx expectedType?

@[builtinTermElab depArrow] def elabDepArrow : TermElab :=
fun stx _ =>
  -- bracktedBinder `->` term
  let binder := stx.getArg 0;
  let term   := stx.getArg 2;
  elabBinders #[binder] $ fun xs => do
    e ← elabType term;
    mkForall stx.val xs e

/-- Main loop `getFunBinderIds?` -/
private partial def getFunBinderIdsAux? : Bool → Syntax → Array Syntax → TermElabM (Option (Array Syntax))
| idOnly, stx, acc =>
  match_syntax stx with
  | `($f $a) =>
     if idOnly then pure none
     else do
       (some acc) ← getFunBinderIdsAux? false f acc | pure none;
       getFunBinderIdsAux? true a acc
  | `(_) => do ident ← mkFreshAnonymousIdent stx; pure (some (acc.push ident))
  | stx  =>
    match stx.isSimpleTermId? with
    | some id => pure (some (acc.push id))
    | _       => pure none

/--
  Auxiliary functions for converting `Term.app ... (Term.app id_1 id_2) ... id_n` into #[id_1, ..., id_m]`
  It is used at `expandFunBinders`. -/
private def getFunBinderIds? (stx : Syntax) : TermElabM (Option (Array Syntax)) :=
getFunBinderIdsAux? false stx #[]

/-- Main loop for `expandFunBinders`. -/
private partial def expandFunBindersAux (binders : Array Syntax) : Syntax → Nat → Array Syntax → TermElabM (Array Syntax × Syntax)
| body, i, newBinders =>
  if h : i < binders.size then
    let binder := binders.get ⟨i, h⟩;
    let processAsPattern : Unit → TermElabM (Array Syntax × Syntax) := fun _ => do {
      let pattern := binder;
      ident ← mkFreshAnonymousIdent binder;
      (binders, newBody) ← expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident mkHole);
      let major := mkTermIdFromIdent ident;
      newBody ← `(match $major with | $pattern => $newBody);
      pure (binders, newBody)
    };
    match binder with
    | Syntax.node `Lean.Parser.Term.hole _ => do
      ident ← mkFreshAnonymousIdent binder;
      let type := binder;
      expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident type)
    | Syntax.node `Lean.Parser.Term.paren args =>
      -- `(` (termParser >> parenSpecial)? `)`
      -- parenSpecial := (tupleTail <|> typeAscription)?
      let binderBody := binder.getArg 1;
      if binderBody.isNone then processAsPattern ()
      else
        let idents  := binderBody.getArg 0;
        let special := binderBody.getArg 1;
        if special.isNone then processAsPattern ()
        else if (special.getArg 0).getKind != `Lean.Parser.Term.typeAscription then processAsPattern ()
        else do
          -- typeAscription := `:` term
          let type := ((special.getArg 0).getArg 1);
          idents? ← getFunBinderIds? idents;
          match idents? with
          | some idents => expandFunBindersAux body (i+1) (newBinders ++ idents.map (fun ident => mkExplicitBinder ident type))
          | none        => processAsPattern ()
    | binder =>
      match binder.isTermId? with
      | some (ident, extra) => do
        unless extra.isNone $ throwError binder "invalid binder, simple identifier expected";
        let type  := mkHole;
        expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident type)
      | none => processAsPattern ()
  else
    pure (newBinders, body)

/--
  Auxiliary function for expanding `fun` notation binders. Recall that `fun` parser is defined as
  ```
  parser! unicodeSymbol "λ" "fun" >> many1 (termParser appPrec) >> unicodeSymbol "⇒" "=>" >> termParser
  ```
  to allow notation such as `fun (a, b) => a + b`, where `(a, b)` should be treated as a pattern.
  The result is pair `(explicitBinders, newBody)`, where `explicitBinders` is syntax of the form
  ```
  `(` ident `:` term `)`
  ```
  which can be elaborated using `elabBinders`, and `newBody` is the updated `body` syntax.
  We update the `body` syntax when expanding the pattern notation.
  Example: `fun (a, b) => a + b` expands into `fun _a_1 => match _a_1 with | (a, b) => a + b`.
  See local function `processAsPattern` at `expandFunBindersAux`. -/
private def expandFunBinders (binders : Array Syntax) (body : Syntax) : TermElabM (Array Syntax × Syntax) :=
expandFunBindersAux binders body 0 #[]

@[builtinTermElab «fun»] def elabFun : TermElab :=
fun stx expectedType? => do
  -- `fun` term+ `=>` term
  let binders := (stx.getArg 1).getArgs;
  let body := stx.getArg 3;
  (binders, body) ← expandFunBinders binders body;
  elabBinders binders $ fun xs => do
    -- TODO: expected type
    e ← elabTerm body none;
    mkLambda stx.val xs e

def withLetDecl {α} (ref : Syntax) (n : Name) (type : Expr) (val : Expr) (k : Expr → TermElabM α) : TermElabM α := do
fvarId ← mkFreshId;
ctx ← read;
let lctx       := ctx.lctx.mkLetDecl fvarId n type val;
let localInsts := ctx.localInstances;
let fvar       := mkFVar fvarId;
c? ← isClass ref type;
match c? with
| some c => adaptReader (fun (ctx : Context) => { lctx := lctx, localInstances := localInsts.push { className := c, fvar := fvar }, .. ctx }) $ k fvar
| none   => adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $ k fvar

def expandOptType (optType : Syntax) : Syntax :=
if optType.isNone then
  mkHole
else
  optType.getArg 1

def elabLetIdDecl (ref : Syntax) (decl body : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
-- `decl` is of the form: ident bracktedBinder+ (`:` term)? `:=` term
let n        := decl.getIdAt 0;
let binders  := (decl.getArg 1).getArgs;
let type     := expandOptType (decl.getArg 2);
let val      := decl.getArg 4;
(type, val) ← elabBinders binders $ fun xs => do {
  type ← elabType type;
  val  ← elabTerm val type;
  type ← mkForall ref xs type;
  val  ← mkLambda ref xs val;
  pure (type, val)
};
trace! `Elab.let.decl (n ++ " : " ++ type ++ " := " ++ val);
withLetDecl ref n type val $ fun x => do
  body ← elabTerm body expectedType?;
  body ← instantiateMVars ref body;
  trace! `Elab.let.body body;
  result ← mkLet ref x body;
  trace! `Elab.let.result result;
  pure result

def elabLetEqnsDecl (ref : Syntax) (decl body : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
throwError decl "not implemented yet"

def elabLetPatDecl (ref : Syntax) (decl body : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
throwError decl "not implemented yet"

@[builtinTermElab «let»] def elabLet : TermElab :=
fun stx expectedType? => do
  -- `let` decl `;` body
  let ref      := stx.val;
  let decl     := stx.getArg 1;
  let body     := stx.getArg 3;
  let declKind := decl.getKind;
  if declKind == `Lean.Parser.Term.letIdDecl then
    elabLetIdDecl ref decl body expectedType?
  else if declKind == `Lean.Parser.Term.letEqns then
    elabLetEqnsDecl ref decl body expectedType?
  else if declKind == `Lean.Parser.Term.letPatDecl then
    elabLetPatDecl ref decl body expectedType?
  else
    throwError ref "unknown let-declaration kind"

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.let;
pure ()

end Term
end Elab
end Lean

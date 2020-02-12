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
namespace Binders
/--
  Given syntax of the forms
    a) (`:` term)?
    b) `:` term
  return `term` if it is present, or a hole if not. -/
private def expandBinderType (stx : Syntax) : Syntax :=
if stx.getNumArgs == 0 then
  mkHole stx
else
  stx.getArg 1

/-- Given syntax of the form `ident <|> hole`, return `ident`. If `hole`, then we create a new anonymous name. -/
private def expandBinderIdent (stx : Syntax) : TermElabM Syntax :=
match_syntax stx with
| `(_) => mkFreshAnonymousIdent stx
| _    => pure stx

/-- Given syntax of the form `(ident >> " : ")?`, return `ident`, or a new instance name. -/
private def expandOptIdent (stx : Syntax) : TermElabM Syntax :=
if stx.getNumArgs == 0 then do
  id ← mkFreshInstanceName; pure $ mkIdentFrom stx id
else
  pure $ stx.getArg 0

structure BinderView :=
(id : Syntax) (type : Syntax) (bi : BinderInfo)

/-
Expand `optional (binderDefault <|> binderTactic)`
def binderDefault := parser! " := " >> termParser
def binderTactic  := parser! " . " >> termParser
-/
private def expandBinderModifier (type : Syntax) (optBinderModifier : Syntax) : TermElabM Syntax :=
if optBinderModifier.isNone then pure type
else
  let modifier := optBinderModifier.getArg 0;
  let kind     := modifier.getKind;
  if kind == `Lean.Parser.Term.binderDefault then do
    let defaultVal := modifier.getArg 1;
    `(optParam $type $defaultVal)
  else if kind == `Lean.Parser.Term.binderTactic then do
    throwError modifier "not implemented yet"
  else
    throwUnsupportedSyntax

private def matchBinder (stx : Syntax) : TermElabM (Array BinderView) :=
match stx with
| Syntax.node k args =>
  if k == `Lean.Parser.Term.simpleBinder then
    -- binderIdent+
    let ids  := (args.get! 0).getArgs;
    let type := mkHole stx;
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.explicitBinder then do
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    let ids         := (args.get! 1).getArgs;
    let type        := expandBinderType (args.get! 2);
    let optModifier := args.get! 3;
    type ← expandBinderModifier type optModifier;
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.implicitBinder then
    -- `{` binderIdent+ binderType `}`
    let ids  := (args.get! 1).getArgs;
    let type := expandBinderType (args.get! 2);
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.implicit }
  else if k == `Lean.Parser.Term.instBinder then do
    -- `[` optIdent type `]`
    id ← expandOptIdent (args.get! 1);
    let type := args.get! 2;
    pure #[ { id := id, type := type, bi := BinderInfo.instImplicit } ]
  else
    throwUnsupportedSyntax
| _ => throwUnsupportedSyntax

structure State :=
(fvars      : Array Expr := #[])
(lctx       : LocalContext)
(localInsts : LocalInstances)

private partial def elabBinderViews (binderViews : Array BinderView) : Nat → State → TermElabM State
| i, s =>
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩;
    withLCtx s.lctx s.localInsts $ do
      type       ← elabType binderView.type;
      fvarId     ← mkFreshFVarId;
      let fvar  := mkFVar fvarId;
      let fvars := s.fvars.push fvar;
      -- dbgTrace (toString binderView.id.getId ++ " : " ++ toString type);
      let lctx  := s.lctx.mkLocalDecl fvarId binderView.id.getId type binderView.bi;
      className? ← isClass binderView.type type;
      match className? with
      | none           => elabBinderViews (i+1) { fvars := fvars, lctx := lctx, .. s }
      | some className => do
        resetSynthInstanceCache;
        let localInsts := s.localInsts.push { className := className, fvar := mkFVar fvarId };
        elabBinderViews (i+1) { fvars := fvars, lctx := lctx, localInsts := localInsts }
  else
    pure s

partial def elabBindersAux (binders : Array Syntax) : Nat → State → TermElabM State
| i, s =>
  if h : i < binders.size then do
    binderViews ← matchBinder (binders.get ⟨i, h⟩);
    s ← elabBinderViews binderViews 0 s;
    elabBindersAux (i+1) s
  else
    pure s

end Binders

/--
  Elaborate the given binders (i.e., `Syntax` objects for `simpleBinder <|> bracktedBinder`),
  update the local context, set of local instances, reset instance chache (if needed), and then
  execute `x` with the updated context. -/
def elabBinders {α} (binders : Array Syntax) (x : Array Expr → TermElabM α) : TermElabM α :=
if binders.isEmpty then x #[]
else do
  lctx ← getLCtx;
  localInsts ← getLocalInsts;
  s ← Binders.elabBindersAux binders 0 { lctx := lctx, localInsts := localInsts };
  resettingSynthInstanceCacheWhen (s.localInsts.size > localInsts.size) $ withLCtx s.lctx s.localInsts $
    x s.fvars

@[inline] def elabBinder {α} (binder : Syntax) (x : Expr → TermElabM α) : TermElabM α :=
elabBinders #[binder] (fun fvars => x (fvars.get! 1))

@[builtinTermElab «forall»] def elabForall : TermElab :=
fun stx _ => match_syntax stx with
| `(forall $binders*, $term) =>
  elabBinders binders $ fun xs => do
    e ← elabType term;
    mkForall stx xs e
| _ => throwUnsupportedSyntax

@[builtinTermElab arrow] def elabArrow : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `($dom:term -> $rng) => `(forall (a : $dom), $rng)
| _                    => throwUnsupportedSyntax

@[builtinTermElab depArrow] def elabDepArrow : TermElab :=
fun stx _ =>
  -- bracktedBinder `->` term
  let binder := stx.getArg 0;
  let term   := stx.getArg 2;
  elabBinders #[binder] $ fun xs => do
    e ← elabType term;
    mkForall stx xs e

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
    match stx.isSimpleTermId? true with
    | some id => pure (some (acc.push id))
    | _       => pure none

/--
  Auxiliary functions for converting `Term.app ... (Term.app id_1 id_2) ... id_n` into `#[id_1, ..., id_m]`
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
      major ← mkFreshAnonymousIdent binder;
      (binders, newBody) ← expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder major (mkHole binder));
      newBody ← `(match $major:ident with | $pattern => $newBody);
      pure (binders, newBody)
    };
    match binder with
    | Syntax.node `Lean.Parser.Term.implicitBinder _ => expandFunBindersAux body (i+1) (newBinders.push binder)
    | Syntax.node `Lean.Parser.Term.instBinder _     => expandFunBindersAux body (i+1) (newBinders.push binder)
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
      match binder.isTermId? true with
      | some (ident, extra) => do
        unless extra.isNone $ throwError binder "invalid binder, simple identifier expected";
        let type  := mkHole binder;
        expandFunBindersAux body (i+1) (newBinders.push $ mkExplicitBinder ident type)
      | none => processAsPattern ()
  else
    pure (newBinders, body)

/--
  Auxiliary function for expanding `fun` notation binders. Recall that `fun` parser is defined as
  ```
  def funBinder : Parser := implicitBinder <|> instBinder <|> termParser appPrec
  parser! unicodeSymbol "λ" "fun" >> many1 funBinder >> unicodeSymbol "⇒" "=>" >> termParser
  ```
  to allow notation such as `fun (a, b) => a + b`, where `(a, b)` should be treated as a pattern.
  The result is a pair `(explicitBinders, newBody)`, where `explicitBinders` is syntax of the form
  ```
  `(` ident `:` term `)`
  ```
  which can be elaborated using `elabBinders`, and `newBody` is the updated `body` syntax.
  We update the `body` syntax when expanding the pattern notation.
  Example: `fun (a, b) => a + b` expands into `fun _a_1 => match _a_1 with | (a, b) => a + b`.
  See local function `processAsPattern` at `expandFunBindersAux`. -/
def expandFunBinders (binders : Array Syntax) (body : Syntax) : TermElabM (Array Syntax × Syntax) :=
expandFunBindersAux binders body 0 #[]

def elabFunCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
-- `fun` term+ `=>` term
let binders := (stx.getArg 1).getArgs;
let body := stx.getArg 3;
(binders, body) ← expandFunBinders binders body;
elabBinders binders $ fun xs => do {
  e ← elabTerm body none;
  mkLambda stx xs e
}

/-
  Recall that
  ```
  def typeSpec := parser! " : " >> termParser
  def optType : Parser := optional typeSpec
  ``` -/
def expandOptType (ref : Syntax) (optType : Syntax) : Syntax :=
if optType.isNone then
  mkHole ref
else
  (optType.getArg 0).getArg 1

def elabLetDeclAux (ref : Syntax) (n : Name) (binders : Array Syntax) (typeStx : Syntax) (valStx : Syntax) (body : Syntax)
    (expectedType? : Option Expr) : TermElabM Expr := do
(type, val) ← elabBinders binders $ fun xs => do {
  type ← elabType typeStx;
  val  ← elabTerm valStx type;
  val  ← ensureHasType valStx type val;
  type ← mkForall ref xs type;
  val  ← mkLambda ref xs val;
  pure (type, val)
};
trace `Elab.let.decl ref $ fun _ => n ++ " : " ++ type ++ " := " ++ val;
withLetDecl ref n type val $ fun x => do
  body ← elabTerm body expectedType?;
  body ← instantiateMVars ref body;
  mkLet ref x body

def elabLetIdDecl (ref : Syntax) (decl body : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
-- `decl` is of the form: ident bracktedBinder+ (`:` term)? `:=` term
let n        := decl.getIdAt 0;
let binders  := (decl.getArg 1).getArgs;
let type     := expandOptType ref (decl.getArg 2);
let val      := decl.getArg 4;
elabLetDeclAux ref n binders type val body expectedType?

@[builtinTermElab «let»] def elabLetDecl : TermElab :=
fun stx expectedType? => match_syntax stx with
| `(let $id:ident $args* := $val; $body) =>
   elabLetDeclAux stx id.getId args (mkHole stx) val body expectedType?
| `(let $id:ident $args* : $type := $val; $body) =>
   elabLetDeclAux stx id.getId args type val body expectedType?
| `(let $pat:term := $val; $body) => do
   stxNew ← `(let x := $val; match x with $pat => $body);
   withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
| `(let $pat:term : $type := $val; $body) => do
   stxNew ← `(let x : $type := $val; match x with $pat => $body);
   withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
| _ => throwUnsupportedSyntax

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.let;
pure ()

end Term
end Elab
end Lean

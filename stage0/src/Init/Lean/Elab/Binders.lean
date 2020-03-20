/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab
namespace Term

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

partial def quoteAutoTactic : Syntax → TermElabM Syntax
| stx@(Syntax.ident _ _ _ _) => throwError stx "invalic auto tactic, identifier is not allowed"
| stx@(Syntax.node k args)   =>
  if Quotation.isAntiquot stx then
    throwError stx "invalic auto tactic, antiquotation is not allowed"
  else do
    empty ← `(Array.empty);
    args ← args.foldlM (fun args arg =>
      if k == nullKind && Quotation.isAntiquotSplice arg then
        throwError arg "invalic auto tactic, antiquotation is not allowed"
      else do
        arg ← quoteAutoTactic arg;
        `(Array.push $args $arg)) empty;
    `(Syntax.node $(quote k) $args)
| Syntax.atom info val => `(Syntax.atom none $(quote val))
| Syntax.missing       => unreachable!

def declareTacticSyntax (tactic : Syntax) : TermElabM Name :=
withFreshMacroScope $ do
  name ← MonadQuotation.addMacroScope `_auto;
  let type := Lean.mkConst `Lean.Syntax;
  tactic ← quoteAutoTactic tactic;
  val ← elabTerm tactic type;
  val ← instantiateMVars tactic val;
  trace `Elab.autoParam tactic $ fun _ => val;
  let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
  addDecl tactic decl;
  compileDecl tactic decl;
  pure name

/-
Expand `optional (binderTactic <|> binderDefault)`
def binderTactic  := parser! " := " >> " by " >> tacticParser
def binderDefault := parser! " := " >> termParser
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
    let tac := modifier.getArg 2;
    name ← declareTacticSyntax tac;
    `(autoParam $type $(mkTermIdFrom tac name))
  else
    throwUnsupportedSyntax

private def getBinderIds (ids : Syntax) : TermElabM (Array Syntax) :=
ids.getArgs.mapM $ fun id =>
  let k := id.getKind;
  if k == identKind || k == `Lean.Parser.Term.hole then
    pure id
  else if k == `Lean.Parser.Term.id && id.getArgs.size == 2 && (id.getArg 1).isNone then
    -- The parser never generates this case, but it is convenient when writting macros.
    pure (id.getArg 0)
  else
    throwError id "identifier or `_` expected"

private def matchBinder (stx : Syntax) : TermElabM (Array BinderView) :=
match stx with
| Syntax.node k args =>
  if k == `Lean.Parser.Term.simpleBinder then do
    -- binderIdent+
    ids ← getBinderIds (args.get! 0);
    let type := mkHole stx;
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.explicitBinder then do
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    ids ← getBinderIds (args.get! 1);
    let type        := expandBinderType (args.get! 2);
    let optModifier := args.get! 3;
    type ← expandBinderModifier type optModifier;
    ids.mapM $ fun id => do id ← expandBinderIdent id; pure { id := id, type := type, bi := BinderInfo.default }
  else if k == `Lean.Parser.Term.implicitBinder then do
    -- `{` binderIdent+ binderType `}`
    ids ← getBinderIds (args.get! 1);
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

private partial def elabBinderViews (binderViews : Array BinderView)
    : Nat → Array Expr → LocalContext → LocalInstances → TermElabM (Array Expr × LocalContext × LocalInstances)
| i, fvars, lctx, localInsts =>
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩;
    withLCtx lctx localInsts $ do
      type       ← elabType binderView.type;
      fvarId     ← mkFreshFVarId;
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
  resettingSynthInstanceCacheWhen (newLocalInsts.size > localInsts.size) $ withLCtx lctx newLocalInsts $
    x fvars

@[inline] def elabBinder {α} (binder : Syntax) (x : Expr → TermElabM α) : TermElabM α :=
elabBinders #[binder] (fun fvars => x (fvars.get! 0))

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

namespace FunBinders

structure State :=
(fvars         : Array Expr := #[])
(lctx          : LocalContext)
(localInsts    : LocalInstances)
(expectedType? : Option Expr := none)
(explicit      : Bool := false)

private def checkNoOptAutoParam (ref : Syntax) (type : Expr) : TermElabM Unit := do
type ← instantiateMVars ref type;
when type.isOptParam $
  throwError ref "optParam is not allowed at 'fun/λ' binders";
when type.isAutoParam $
  throwError ref "autoParam is not allowed at 'fun/λ' binders"

private def propagateExpectedType (ref : Syntax) (fvar : Expr) (fvarType : Expr) (s : State) : TermElabM State := do
match s.expectedType? with
| none              => pure s
| some expectedType => do
  expectedType ← whnfForall ref expectedType;
  match expectedType with
  | Expr.forallE _ d b _ => do
    isDefEq ref fvarType d;
    checkNoOptAutoParam ref fvarType;
    let b := b.instantiate1 fvar;
    pure { expectedType? := some b, .. s }
  | _ => pure { expectedType? := none, .. s }

private partial def elabFunBinderViews (binderViews : Array BinderView) : Nat → State → TermElabM State
| i, s =>
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩;
    withLCtx s.lctx s.localInsts $ do
      /- As soon as we find an explicit binder, we switch to `explict := true` mode. -/
      let s     := if binderView.bi.isExplicit then { explicit := true, .. s } else s;
      type       ← elabType binderView.type;
      checkNoOptAutoParam binderView.type type;
      fvarId ← mkFreshFVarId;
      let fvar  := mkFVar fvarId;
      let s     := { fvars := s.fvars.push fvar, .. s };
      let continue (s : State) : TermElabM State := do {
        className? ← isClass binderView.type type;
        match className? with
        | none           => elabFunBinderViews (i+1) s
        | some className => do
          resetSynthInstanceCache;
          let localInsts := s.localInsts.push { className := className, fvar := mkFVar fvarId };
          elabFunBinderViews (i+1) { localInsts := localInsts, .. s }
      };
      if s.explicit then do
        -- dbgTrace (toString binderView.id.getId ++ " : " ++ toString type);
        /-
          We do **not** want to support default and auto arguments in lambda abstractions.
          Example: `fun (x : Nat := 10) => x+1`.
          We do not believe this is an useful feature, and it would complicate the logic here.
        -/
        let lctx  := s.lctx.mkLocalDecl fvarId binderView.id.getId type binderView.bi;
        s ← propagateExpectedType binderView.id fvar type s;
        continue { lctx := lctx, .. s }
      else do
        /- When `@` is not used, we use let-declarations to elaborate the implicit binders
           occurring in a prefix of lambda abstraction.
           For example, `fun {α} => b` is elaborated into `let α := ?m; b`.
           We do this because we can propagate the expected type more effectively.
           Recall that, a term `fun {α} => b` has to be elaborated as `(fun α => b) ?m` where
           `?m` is a fresh metavariable for the implicit argument `{α}`.
           `let α := ?m; b` is the same expression after beta-reduction, but we can elaborate
           `b` using the expected type for `fun {α} => b`.

           This design decision is also motivated by the implicit lambda feature.
           For example, suppose we have
           ```
           def id : {α : Type} → α → α :=
           fun {α} x => @id α x
           ```
           When the elaborator reaches `fun {α} x => id x` the expected type is `{α : Type} → α → α`.
           Then, it introduces a new local variable `α_1` for the implict binder, and elaborates
           `fun {α} x => @id α x` with expected type `α_1 → α_1`.
           Then, the elaborator reaches this branch, and creates the let declaration `α : ?t_1 := ?mvar`,
           Note that `type` is the metavariable `?t_1` in this example since we de not specify any type at `{α}`.
           Then, it elaborates `fun x => @id α x` still using the expected type `α_1 → α_1`.
           When it reaches the binder `x`, it creates the variable `x : ?t_1`, and `propagateExpectedType` creates
           the unification problem `?t_1 =?= α_1` which is solved `?t_1 := α_1`. Then, when it elaborates
           `@id α x`, the unification constraint `α =?= α_1` is created. The unifier (aka `isDefEq`), zeta-reduce ‵α`
           and reduces the constraint to `?mvar =?= α_1`, which is solved `?mvar := α_1`, their type are also unified
           which produces the assignment `?t_1 := Type`. Thus, the resulting expression is:
           ```
           def id : {α : Type} → α → α :=
           fun {α_1} => let α : Type := α_1; fun (x : α_1) => @id α x
           ```
           It is also matches the intuition that lambda binders {α} are useful for naming binders produced by
           the implicit lambda feature.
        -/
        mvar ← mkFreshExprMVar binderView.id type;
        let lctx := s.lctx.mkLetDecl fvarId binderView.id.getId type mvar;
        continue { lctx := lctx, .. s }
  else
    pure s

partial def elabFunBindersAux (binders : Array Syntax) : Nat → State → TermElabM State
| i, s =>
  if h : i < binders.size then do
    binderViews ← matchBinder (binders.get ⟨i, h⟩);
    s ← elabFunBinderViews binderViews 0 s;
    elabFunBindersAux (i+1) s
  else
    pure s

end FunBinders

def elabFunBinders {α} (binders : Array Syntax) (expectedType? : Option Expr) (explicit : Bool) (x : Array Expr → Option Expr → TermElabM α) : TermElabM α :=
if binders.isEmpty then x #[] expectedType?
else do
  lctx ← getLCtx;
  localInsts ← getLocalInsts;
  s ← FunBinders.elabFunBindersAux binders 0 { lctx := lctx, localInsts := localInsts, expectedType? := expectedType?, explicit := explicit };
  resettingSynthInstanceCacheWhen (s.localInsts.size > localInsts.size) $ withLCtx s.lctx s.localInsts $
    x s.fvars s.expectedType?

def elabFunCore (stx : Syntax) (expectedType? : Option Expr) (explicit : Bool) : TermElabM Expr := do
-- `fun` term+ `=>` term
let binders := (stx.getArg 1).getArgs;
let body := stx.getArg 3;
(binders, body) ← expandFunBinders binders body;
elabFunBinders binders expectedType? explicit $ fun xs expectedType? => do {
  e ← elabTerm body expectedType?;
  mkLambda stx xs e
}

@[builtinTermElab «fun»] def elabFun : TermElab :=
fun stx expectedType? => elabFunCore stx expectedType? false

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

/- If `useLetExpr` is true, then a kernel let-expression `let x : type := val; body` is created.
   Otherwise, we create a term of the form `(fun (x : type) => body) val` -/
def elabLetDeclAux (ref : Syntax) (n : Name) (binders : Array Syntax) (typeStx : Syntax) (valStx : Syntax) (body : Syntax)
    (expectedType? : Option Expr) (useLetExpr : Bool) : TermElabM Expr := do
(type, val) ← elabBinders binders $ fun xs => do {
  type ← elabType typeStx;
  val  ← elabTerm valStx type;
  val  ← ensureHasType valStx type val;
  type ← mkForall ref xs type;
  val  ← mkLambda ref xs val;
  pure (type, val)
};
trace `Elab.let.decl ref $ fun _ => n ++ " : " ++ type ++ " := " ++ val;
if useLetExpr then
  withLetDecl ref n type val $ fun x => do
    body ← elabTerm body expectedType?;
    body ← instantiateMVars ref body;
    mkLet ref x body
else do
  f ← withLocalDecl ref n BinderInfo.default type $ fun x => do {
    body ← elabTerm body expectedType?;
    body ← instantiateMVars ref body;
    mkLambda ref #[x] body
  };
  pure $ mkApp f val

@[builtinTermElab «let»] def elabLetDecl : TermElab :=
fun stx expectedType? => match_syntax stx with
| `(let $id:ident $args* := $val; $body) =>
   elabLetDeclAux stx id.getId args (mkHole stx) val body expectedType? true
| `(let $id:ident $args* : $type := $val; $body) =>
   elabLetDeclAux stx id.getId args type val body expectedType? true
| `(let $pat:term := $val; $body) => do
   stxNew ← `(let x := $val; match x with $pat => $body);
   withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
| `(let $pat:term : $type := $val; $body) => do
   stxNew ← `(let x : $type := $val; match x with $pat => $body);
   withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
| _ => throwUnsupportedSyntax

@[builtinTermElab «let!»] def elabLetBangDecl : TermElab :=
fun stx expectedType? => match_syntax stx with
| `(let! $id:ident $args* := $val; $body) =>
   elabLetDeclAux stx id.getId args (mkHole stx) val body expectedType? false
| `(let! $id:ident $args* : $type := $val; $body) =>
   elabLetDeclAux stx id.getId args type val body expectedType? false
| `(let! $pat:term := $val; $body) => do
   stxNew ← `(let! x := $val; match x with $pat => $body);
   withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
| `(let! $pat:term : $type := $val; $body) => do
   stxNew ← `(let! x : $type := $val; match x with $pat => $body);
   withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
| _ => throwUnsupportedSyntax

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.let;
pure ()

end Term
end Elab
end Lean

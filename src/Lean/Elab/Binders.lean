/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Elab.Quotation

namespace Lean.Elab.Term
open Meta

/--
  Given syntax of the forms
    a) (`:` term)?
    b) `:` term
  return `term` if it is present, or a hole if not. -/
private def expandBinderType (ref : Syntax) (stx : Syntax) : Syntax :=
  if stx.getNumArgs == 0 then
    mkHole ref
  else
    stx[1]

/-- Given syntax of the form `ident <|> hole`, return `ident`. If `hole`, then we create a new anonymous name. -/
private def expandBinderIdent (stx : Syntax) : TermElabM Syntax :=
  match_syntax stx with
  | `(_) => mkFreshIdent stx
  | _    => pure stx

/-- Given syntax of the form `(ident >> " : ")?`, return `ident`, or a new instance name. -/
private def expandOptIdent (stx : Syntax) : TermElabM Syntax := do
  if stx.getNumArgs == 0 then
    pure $ mkIdentFrom stx (← mkFreshInstanceName)
  else
    pure stx[0]

structure BinderView :=
  (id : Syntax)
  (type : Syntax)
  (bi : BinderInfo)

partial def quoteAutoTactic : Syntax → TermElabM Syntax
  | stx@(Syntax.ident _ _ _ _) => throwErrorAt stx "invalic auto tactic, identifier is not allowed"
  | stx@(Syntax.node k args)   => do
    if stx.isAntiquot then
      throwErrorAt stx "invalic auto tactic, antiquotation is not allowed"
    else
      let quotedArgs ← `(Array.empty)
      for arg in args do
        if k == nullKind && Quotation.isAntiquotSplice arg then
          throwErrorAt arg "invalic auto tactic, antiquotation is not allowed"
        else
          let quotedArg ← quoteAutoTactic arg
          quotedArgs ← `(Array.push $quotedArgs $quotedArg)
      `(Syntax.node $(quote k) $quotedArgs)
  | Syntax.atom info val => `(Syntax.atom {} $(quote val))
  | Syntax.missing       => unreachable!

def declareTacticSyntax (tactic : Syntax) : TermElabM Name :=
  withFreshMacroScope do
    let name ← MonadQuotation.addMacroScope `_auto
    let type := Lean.mkConst `Lean.Syntax
    let tactic ← quoteAutoTactic tactic
    let val ← elabTerm tactic type
    let val ← instantiateMVars val
    trace[Elab.autoParam]! val
    let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false }
    addDecl decl
    compileDecl decl
    pure name

/-
Expand `optional (binderTactic <|> binderDefault)`
def binderTactic  := parser! " := " >> " by " >> tacticParser
def binderDefault := parser! " := " >> termParser
-/
private def expandBinderModifier (type : Syntax) (optBinderModifier : Syntax) : TermElabM Syntax := do
  if optBinderModifier.isNone then
    pure type
  else
    let modifier := optBinderModifier[0]
    let kind     := modifier.getKind
    if kind == `Lean.Parser.Term.binderDefault then
      let defaultVal := modifier[1]
      `(optParam $type $defaultVal)
    else if kind == `Lean.Parser.Term.binderTactic then
      let tac := modifier[2]
      let name ← declareTacticSyntax tac
      `(autoParam $type $(mkIdentFrom tac name))
    else
      throwUnsupportedSyntax

private def getBinderIds (ids : Syntax) : TermElabM (Array Syntax) :=
  ids.getArgs.mapM fun id =>
    let k := id.getKind
    if k == identKind || k == `Lean.Parser.Term.hole then
      pure id
    else
      throwErrorAt id "identifier or `_` expected"

private def matchBinder (stx : Syntax) : TermElabM (Array BinderView) :=
  match stx with
  | Syntax.node k args => do
    if k == `Lean.Parser.Term.simpleBinder then
      -- binderIdent+
      let ids ← getBinderIds args[0]
      let type := mkHole stx
      ids.mapM fun id => do pure { id := (← expandBinderIdent id), type := type, bi := BinderInfo.default }
    else if k == `Lean.Parser.Term.explicitBinder then
      -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
      let ids ← getBinderIds args[1]
      let type        := expandBinderType stx args[2]
      let optModifier := args[3]
      let type ← expandBinderModifier type optModifier
      ids.mapM fun id => do pure { id := (← expandBinderIdent id), type := type, bi := BinderInfo.default }
    else if k == `Lean.Parser.Term.implicitBinder then
      -- `{` binderIdent+ binderType `}`
      let ids ← getBinderIds args[1]
      let type := expandBinderType stx args[2]
      ids.mapM fun id => do pure { id := (← expandBinderIdent id), type := type, bi := BinderInfo.implicit }
    else if k == `Lean.Parser.Term.instBinder then
      -- `[` optIdent type `]`
      let id ← expandOptIdent args[1]
      let type := args[2]
      pure #[ { id := id, type := type, bi := BinderInfo.instImplicit } ]
    else
      throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

private def registerFailedToInferBinderTypeInfo (type : Expr) (ref : Syntax) : TermElabM Unit :=
  registerCustomErrorIfMVar type ref "failed to infer binder type"

private partial def elabBinderViews (binderViews : Array BinderView)
    (i : Nat) (fvars : Array Expr) (lctx : LocalContext) (localInsts : LocalInstances) : TermElabM (Array Expr × LocalContext × LocalInstances) :=
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩
    withRef binderView.type $ withLCtx lctx localInsts do
      let type ← elabType binderView.type
      registerFailedToInferBinderTypeInfo type binderView.type
      let fvarId ← mkFreshFVarId
      let fvar  := mkFVar fvarId
      let fvars := fvars.push fvar
      let lctx  := lctx.mkLocalDecl fvarId binderView.id.getId type binderView.bi
      match (← isClass? type) with
      | none           => elabBinderViews binderViews (i+1) fvars lctx localInsts
      | some className =>
        resettingSynthInstanceCache do
          let localInsts := localInsts.push { className := className, fvar := mkFVar fvarId }
          elabBinderViews binderViews (i+1) fvars lctx localInsts
  else
    pure (fvars, lctx, localInsts)

private partial def elabBindersAux (binders : Array Syntax)
    (i : Nat) (fvars : Array Expr) (lctx : LocalContext) (localInsts : LocalInstances) : TermElabM (Array Expr × LocalContext × LocalInstances) := do
  if h : i < binders.size then
    let binderViews ← matchBinder (binders.get ⟨i, h⟩)
    let (fvars, lctx, localInsts) ← elabBinderViews binderViews 0 fvars lctx localInsts
    elabBindersAux binders (i+1) fvars lctx localInsts
  else
    pure (fvars, lctx, localInsts)

/--
  Elaborate the given binders (i.e., `Syntax` objects for `simpleBinder <|> bracketedBinder`),
  update the local context, set of local instances, reset instance chache (if needed), and then
  execute `x` with the updated context. -/
def elabBinders {α} (binders : Array Syntax) (x : Array Expr → TermElabM α) : TermElabM α := do
  if binders.isEmpty then
    x #[]
  else
    let lctx ← getLCtx
    let localInsts ← getLocalInstances
    let (fvars, lctx, newLocalInsts) ← elabBindersAux binders 0 #[] lctx localInsts
    resettingSynthInstanceCacheWhen (newLocalInsts.size > localInsts.size) $ withLCtx lctx newLocalInsts $
      x fvars

@[inline] def elabBinder {α} (binder : Syntax) (x : Expr → TermElabM α) : TermElabM α :=
  elabBinders #[binder] (fun fvars => x (fvars.get! 0))

@[builtinTermElab «forall»] def elabForall : TermElab := fun stx _ =>
  match_syntax stx with
  | `(forall $binders*, $term) =>
    elabBinders binders fun xs => do
      let e ← elabType term
      mkForallFVars xs e
  | _ => throwUnsupportedSyntax

@[builtinTermElab arrow] def elabArrow : TermElab :=
  adaptExpander fun stx => match_syntax stx with
  | `($dom:term -> $rng) => `(forall (a : $dom), $rng)
  | _                    => throwUnsupportedSyntax

@[builtinTermElab depArrow] def elabDepArrow : TermElab := fun stx _ =>
  -- bracketedBinder `->` term
  let binder := stx[0]
  let term   := stx[2]
  elabBinders #[binder] fun xs => do
    mkForallFVars xs (← elabType term)

/--
  Auxiliary functions for converting `Term.app ... (Term.app id_1 id_2) ... id_n` into `#[id_1, ..., id_m]`
  It is used at `expandFunBinders`. -/
private partial def getFunBinderIds? (stx : Syntax) : TermElabM (Option (Array Syntax)) :=
  let rec loop (idOnly : Bool) (stx : Syntax) (acc : Array Syntax) :=
    match_syntax stx with
    | `($f $a) => do
       if idOnly then
         pure none
       else
         let (some acc) ← loop false f acc | pure none
         loop true a acc
    | `(_) => do let ident ← mkFreshIdent stx; pure (some (acc.push ident))
    | `($id:ident) => pure (some (acc.push id))
    | _ => pure none
  loop false stx #[]

/--
  Auxiliary function for expanding `fun` notation binders. Recall that `fun` parser is defined as
  ```
  def funBinder : Parser := implicitBinder <|> instBinder <|> termParser maxPrec
  parser! unicodeSymbol "λ" "fun" >> many1 funBinder >> "=>" >> termParser
  ```
  to allow notation such as `fun (a, b) => a + b`, where `(a, b)` should be treated as a pattern.
  The result is a pair `(explicitBinders, newBody)`, where `explicitBinders` is syntax of the form
  ```
  `(` ident `:` term `)`
  ```
  which can be elaborated using `elabBinders`, and `newBody` is the updated `body` syntax.
  We update the `body` syntax when expanding the pattern notation.
  Example: `fun (a, b) => a + b` expands into `fun _a_1 => match _a_1 with | (a, b) => a + b`.
  See local function `processAsPattern` at `expandFunBindersAux`.

  The resulting `Bool` is true if a pattern was found. We use it "mark" a macro expansion. -/
partial def expandFunBinders (binders : Array Syntax) (body : Syntax) : TermElabM (Array Syntax × Syntax × Bool) :=
  let rec loop (body : Syntax) (i : Nat) (newBinders : Array Syntax) := do
    if h : i < binders.size then
      let binder := binders.get ⟨i, h⟩
      let processAsPattern : Unit → TermElabM (Array Syntax × Syntax × Bool) := fun _ => do
        let pattern := binder
        let major ← mkFreshIdent binder
        let (binders, newBody, _) ← loop body (i+1) (newBinders.push $ mkExplicitBinder major (mkHole binder))
        let newBody ← `(match $major:ident with | $pattern => $newBody)
        pure (binders, newBody, true)
      match binder with
      | Syntax.node `Lean.Parser.Term.implicitBinder _ => loop body (i+1) (newBinders.push binder)
      | Syntax.node `Lean.Parser.Term.instBinder _     => loop body (i+1) (newBinders.push binder)
      | Syntax.node `Lean.Parser.Term.explicitBinder _ => loop body (i+1) (newBinders.push binder)
      | Syntax.node `Lean.Parser.Term.hole _ =>
        let ident ← mkFreshIdent binder
        let type := binder
        loop body (i+1) (newBinders.push $ mkExplicitBinder ident type)
      | Syntax.node `Lean.Parser.Term.paren args =>
        -- `(` (termParser >> parenSpecial)? `)`
        -- parenSpecial := (tupleTail <|> typeAscription)?
        let binderBody := binder[1]
        if binderBody.isNone then processAsPattern ()
        else
          let idents  := binderBody[0]
          let special := binderBody[1]
          if special.isNone then processAsPattern ()
          else if special[0].getKind != `Lean.Parser.Term.typeAscription then
            processAsPattern ()
          else
            -- typeAscription := `:` term
            let type := special[0][1]
            match (← getFunBinderIds? idents) with
            | some idents => loop body (i+1) (newBinders ++ idents.map (fun ident => mkExplicitBinder ident type))
            | none        => processAsPattern ()
      | Syntax.ident _ _ _ _ =>
        let type  := mkHole binder
        loop body (i+1) (newBinders.push $ mkExplicitBinder binder type)
      | _ => processAsPattern ()
    else
      pure (newBinders, body, false)
  loop body 0 #[]

namespace FunBinders

structure State :=
  (fvars         : Array Expr := #[])
  (lctx          : LocalContext)
  (localInsts    : LocalInstances)
  (expectedType? : Option Expr := none)

private def propagateExpectedType (fvar : Expr) (fvarType : Expr) (s : State) : TermElabM State := do
  match s.expectedType? with
  | none              => pure s
  | some expectedType =>
    let expectedType ← whnfForall expectedType
    match expectedType with
    | Expr.forallE _ d b _ =>
      isDefEq fvarType d
      let b := b.instantiate1 fvar
      pure { s with expectedType? := some b }
    | _ => pure { s with expectedType? := none }

private partial def elabFunBinderViews (binderViews : Array BinderView) (i : Nat) (s : State) : TermElabM State :=
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩
    withRef binderView.type $ withLCtx s.lctx s.localInsts do
      let type       ← elabType binderView.type
      registerFailedToInferBinderTypeInfo type binderView.type
      let fvarId ← mkFreshFVarId
      let fvar  := mkFVar fvarId
      let s     := { s with fvars := s.fvars.push fvar }
      -- dbgTrace (toString binderView.id.getId ++ " : " ++ toString type)
      /-
        We do **not** want to support default and auto arguments in lambda abstractions.
        Example: `fun (x : Nat := 10) => x+1`.
        We do not believe this is an useful feature, and it would complicate the logic here.
      -/
      let lctx  := s.lctx.mkLocalDecl fvarId binderView.id.getId type binderView.bi
      let s ← withRef binderView.id $ propagateExpectedType fvar type s
      let s := { s with lctx := lctx }
      match (← isClass? type) with
      | none           => elabFunBinderViews binderViews (i+1) s
      | some className =>
        resettingSynthInstanceCache do
          let localInsts := s.localInsts.push { className := className, fvar := mkFVar fvarId }
          elabFunBinderViews binderViews (i+1) { s with localInsts := localInsts }
  else
    pure s

partial def elabFunBindersAux (binders : Array Syntax) (i : Nat) (s : State) : TermElabM State := do
  if h : i < binders.size then
    let binderViews ← matchBinder (binders.get ⟨i, h⟩)
    let s ← elabFunBinderViews binderViews 0 s
    elabFunBindersAux binders (i+1) s
  else
    pure s

end FunBinders

def elabFunBinders {α} (binders : Array Syntax) (expectedType? : Option Expr) (x : Array Expr → Option Expr → TermElabM α) : TermElabM α :=
  if binders.isEmpty then
    x #[] expectedType?
  else do
    let lctx ← getLCtx
    let localInsts ← getLocalInstances
    let s ← FunBinders.elabFunBindersAux binders 0 { lctx := lctx, localInsts := localInsts, expectedType? := expectedType? }
    resettingSynthInstanceCacheWhen (s.localInsts.size > localInsts.size) $ withLCtx s.lctx s.localInsts $
      x s.fvars s.expectedType?

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
    optType[0][1]

/- Helper function for `expandEqnsIntoMatch` -/
private def getMatchAltNumPatterns (matchAlts : Syntax) : Nat :=
  let alt0 := matchAlts[1][0]
  let pats := alt0[0].getSepArgs
  pats.size

/- Helper function for `expandMatchAltsIntoMatch` -/
private def expandMatchAltsIntoMatchAux (ref : Syntax) (matchAlts : Syntax) (matchTactic : Bool) : Nat → Array Syntax → MacroM Syntax
  | 0,   discrs =>
    pure $ Syntax.node (if matchTactic then `Lean.Parser.Tactic.match else `Lean.Parser.Term.match)
      #[mkAtomFrom ref "match ", mkNullNode discrs, mkNullNode, mkAtomFrom ref " with ", matchAlts]
  | n+1, discrs => withFreshMacroScope do
    let x ← `(x)
    let discrs := if discrs.isEmpty then discrs else discrs.push $ mkAtomFrom ref ", "
    let discrs := discrs.push $ Syntax.node `Lean.Parser.Term.matchDiscr #[mkNullNode, x]
    let body ← expandMatchAltsIntoMatchAux ref matchAlts matchTactic n discrs
    if matchTactic then
      `(tactic| intro $x:term; $body:tactic)
    else
      `(@fun $x => $body)

/--
  Expand `matchAlts` syntax into a full `match`-expression.
  Example
    ```
    | 0, true => alt_1
    | i, _    => alt_2
    ```
    expands intro (for tactic == false)
    ```
    fun x_1 x_2 =>
    match x_1, x_2 with
    | 0, true => alt_1
    | i, _    => alt_2
    ```
    and (for tactic == true)
    ```
    intro x_1; intro x_2;
    match x_1, x_2 with
    | 0, true => alt_1
    | i, _    => alt_2
    ```
 -/
def expandMatchAltsIntoMatch (ref : Syntax) (matchAlts : Syntax) (tactic := false) : MacroM Syntax :=
  expandMatchAltsIntoMatchAux ref matchAlts tactic (getMatchAltNumPatterns matchAlts) #[]

def expandMatchAltsIntoMatchTactic (ref : Syntax) (matchAlts : Syntax) : MacroM Syntax :=
  expandMatchAltsIntoMatchAux ref matchAlts true (getMatchAltNumPatterns matchAlts) #[]

@[builtinTermElab «fun»] def elabFun : TermElab := fun stx expectedType? => do
  -- "fun " >> ((many1 funBinder >> darrow >> termParser) <|> matchAlts)
  if stx[1].isOfKind `Lean.Parser.Term.matchAlts then
    let stxNew ← liftMacroM $ expandMatchAltsIntoMatch stx stx[1]
    withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  else
    let binders := stx[1].getArgs
    let body := stx[3]
    let (binders, body, expandedPattern) ← expandFunBinders binders body
    if expandedPattern then
      let newStx ← `(fun $binders* => $body)
      withMacroExpansion stx newStx $ elabTerm newStx expectedType?
    else
      elabFunBinders binders expectedType? fun xs expectedType? => do
        /- We ensure the expectedType here since it will force coercions to be applied if needed.
           If we just use `elabTerm`, then we will need to a coercion `Coe (α → β) (α → δ)` whenever there is a coercion `Coe β δ`,
           and another instance for the dependent version. -/
        let e ← elabTermEnsuringType body expectedType?
        mkLambdaFVars xs e

/- If `useLetExpr` is true, then a kernel let-expression `let x : type := val; body` is created.
   Otherwise, we create a term of the form `(fun (x : type) => body) val`

   The default elaboration order is `binders`, `typeStx`, `valStx`, and `body`.
   If `elabBodyFirst == true`, then we use the order `binders`, `typeStx`, `body`, and `valStx`. -/
def elabLetDeclAux (n : Name) (binders : Array Syntax) (typeStx : Syntax) (valStx : Syntax) (body : Syntax)
    (expectedType? : Option Expr) (useLetExpr : Bool) (elabBodyFirst : Bool) : TermElabM Expr := do
  let (type, val, arity) ← elabBinders binders fun xs => do
    let type ← elabType typeStx
    registerCustomErrorIfMVar type typeStx "failed to infer 'let' declaration type"
    if elabBodyFirst then
      let type ← mkForallFVars xs type
      let val  ← mkFreshExprMVar type
      pure (type, val, xs.size)
    else
      let val  ← elabTermEnsuringType valStx type
      let type ← mkForallFVars xs type
      let val  ← mkLambdaFVars xs val
      pure (type, val, xs.size)
  trace[Elab.let.decl]! "{n} : {type} := {val}"
  let result ←
    if useLetExpr then
      withLetDecl n type val fun x => do
        let body ← elabTerm body expectedType?
        let body ← instantiateMVars body
        mkLetFVars #[x] body
    else
      let f ← withLocalDecl n BinderInfo.default type fun x => do
        let body ← elabTerm body expectedType?
        let body ← instantiateMVars body
        mkLambdaFVars #[x] body
      pure $ mkApp f val
  if elabBodyFirst then
    forallBoundedTelescope type arity fun xs type => do
      let valResult ← elabTermEnsuringType valStx type
      let valResult ← mkLambdaFVars xs valResult
      unless (← isDefEq val valResult) do
        throwError "unexpected error when elaborating 'let'"
  pure result

structure LetIdDeclView :=
  (id      : Name)
  (binders : Array Syntax)
  (type    : Syntax)
  (value   : Syntax)

def mkLetIdDeclView (letIdDecl : Syntax) : LetIdDeclView :=
  -- `letIdDecl` is of the form `ident >> many bracketedBinder >> optType >> " := " >> termParser
  let id      := letIdDecl[0].getId
  let binders := letIdDecl[1].getArgs
  let optType := letIdDecl[2]
  let type    := expandOptType letIdDecl optType
  let value   := letIdDecl[4]
  { id := id, binders := binders, type := type, value := value }

private def expandLetEqnsDeclVal (ref : Syntax) (alts : Syntax) : Nat → Array Syntax → MacroM Syntax
  | 0,   discrs =>
    pure $ Syntax.node `Lean.Parser.Term.match
      #[mkAtomFrom ref "match ", mkNullNode discrs, mkNullNode, mkAtomFrom ref " with ", alts]
  | n+1, discrs => withFreshMacroScope do
    let x ← `(x)
    let discrs := if discrs.isEmpty then discrs else discrs.push $ mkAtomFrom ref ", "
    let discrs := discrs.push $ Syntax.node `Lean.Parser.Term.matchDiscr #[mkNullNode, x]
    let body ← expandLetEqnsDeclVal ref alts n discrs
    `(fun $x => $body)

def expandLetEqnsDecl (letDecl : Syntax) : MacroM Syntax := do
  let ref       := letDecl
  let matchAlts := letDecl[3]
  let val ← expandMatchAltsIntoMatch ref matchAlts
  pure $ Syntax.node `Lean.Parser.Term.letIdDecl #[letDecl[0], letDecl[1], letDecl[2], mkAtomFrom ref " := ", val]

def elabLetDeclCore (stx : Syntax) (expectedType? : Option Expr) (useLetExpr : Bool) (elabBodyFirst : Bool) : TermElabM Expr := do
  let ref     := stx
  let letDecl := stx[1][0]
  let body    := stx[3]
  if letDecl.getKind == `Lean.Parser.Term.letIdDecl then
    let { id := id, binders := binders, type := type, value := val } := mkLetIdDeclView letDecl
    elabLetDeclAux id binders type val body expectedType? useLetExpr elabBodyFirst
  else if letDecl.getKind == `Lean.Parser.Term.letPatDecl then
    -- node `Lean.Parser.Term.letPatDecl  $ try (termParser >> pushNone >> optType >> " := ") >> termParser
    let pat     := letDecl[0]
    let optType := letDecl[2]
    let type    := expandOptType stx optType
    let val     := letDecl[4]
    let stxNew ← `(let x : $type := $val; match x with | $pat => $body)
    let stxNew  := match useLetExpr, elabBodyFirst with
      | true,  false => stxNew
      | true,  true  => stxNew.updateKind `Lean.Parser.Term.«let*»
      | false, true  => stxNew.updateKind `Lean.Parser.Term.«let!»
      | false, false => unreachable!
    withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  else if letDecl.getKind == `Lean.Parser.Term.letEqnsDecl then
    let letDeclIdNew ← liftMacroM $ expandLetEqnsDecl letDecl
    let declNew := stx[1].setArg 0 letDeclIdNew
    let stxNew  := stx.setArg 1 declNew
    withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  else
    throwUnsupportedSyntax

@[builtinTermElab «let»] def elabLetDecl : TermElab :=
  fun stx expectedType? => elabLetDeclCore stx expectedType? true false

@[builtinTermElab «let!»] def elabLetBangDecl : TermElab :=
  fun stx expectedType? => elabLetDeclCore stx expectedType? false false

@[builtinTermElab «let*»] def elabLetStarDecl : TermElab :=
  fun stx expectedType? => elabLetDeclCore stx expectedType? true true

builtin_initialize registerTraceClass `Elab.let

end Lean.Elab.Term

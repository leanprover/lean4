/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term
import Lean.Parser.Term

namespace Lean.Elab.Term
open Meta
open Lean.Parser.Term

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
  match stx with
  | `(_) => mkFreshIdent stx
  | _    => pure stx

/-- Given syntax of the form `(ident >> " : ")?`, return `ident`, or a new instance name. -/
private def expandOptIdent (stx : Syntax) : TermElabM Syntax := do
  if stx.isNone then
    let id ← withFreshMacroScope <| MonadQuotation.addMacroScope `inst
    return mkIdentFrom stx id
  else
    return stx[0]

structure BinderView where
  id : Syntax
  type : Syntax
  bi : BinderInfo

partial def quoteAutoTactic : Syntax → TermElabM Syntax
  | stx@(Syntax.ident _ _ _ _) => throwErrorAt stx "invalid auto tactic, identifier is not allowed"
  | stx@(Syntax.node k args)   => do
    if stx.isAntiquot then
      throwErrorAt stx "invalid auto tactic, antiquotation is not allowed"
    else
      let mut quotedArgs ← `(Array.empty)
      for arg in args do
        if k == nullKind && (arg.isAntiquotSuffixSplice || arg.isAntiquotSplice) then
          throwErrorAt arg "invalid auto tactic, antiquotation is not allowed"
        else
          let quotedArg ← quoteAutoTactic arg
          quotedArgs ← `(Array.push $quotedArgs $quotedArg)
      `(Syntax.node $(quote k) $quotedArgs)
  | Syntax.atom info val => `(mkAtom $(quote val))
  | Syntax.missing       => unreachable!

def declareTacticSyntax (tactic : Syntax) : TermElabM Name :=
  withFreshMacroScope do
    let name ← MonadQuotation.addMacroScope `_auto
    let type := Lean.mkConst `Lean.Syntax
    let tactic ← quoteAutoTactic tactic
    let val ← elabTerm tactic type
    let val ← instantiateMVars val
    trace[Elab.autoParam] val
    let decl := Declaration.defnDecl { name := name, levelParams := [], type := type, value := val, hints := ReducibilityHints.opaque,
                                       safety := DefinitionSafety.safe }
    addDecl decl
    compileDecl decl
    return name

/-
Expand `optional (binderTactic <|> binderDefault)`
def binderTactic  := parser! " := " >> " by " >> tacticParser
def binderDefault := parser! " := " >> termParser
-/
private def expandBinderModifier (type : Syntax) (optBinderModifier : Syntax) : TermElabM Syntax := do
  if optBinderModifier.isNone then
    return type
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
      return id
    else
      throwErrorAt id "identifier or `_` expected"

/-
  Recall that
  ```
  def typeSpec := parser! " : " >> termParser
  def optType : Parser := optional typeSpec
  ```
-/
def expandOptType (ref : Syntax) (optType : Syntax) : Syntax :=
  if optType.isNone then
    mkHole ref
  else
    optType[0][1]

private def matchBinder (stx : Syntax) : TermElabM (Array BinderView) :=
  match stx with
  | Syntax.node k args => do
    if k == `Lean.Parser.Term.simpleBinder then
      -- binderIdent+ >> optType
      let ids ← getBinderIds args[0]
      let type := expandOptType stx args[1]
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

private def addLocalVarInfoCore (lctx : LocalContext) (stx : Syntax) (fvar : Expr) : TermElabM Unit := do
  if (← getInfoState).enabled then
    pushInfoTree <| InfoTree.node (children := {}) <| Info.ofTermInfo { lctx := lctx, expr := fvar, stx := stx }

private def addLocalVarInfo (stx : Syntax) (fvar : Expr) : TermElabM Unit := do
  addLocalVarInfoCore (← getLCtx) stx fvar

private def ensureAtomicBinderName (binderView : BinderView) : TermElabM Unit :=
  let n := binderView.id.getId.eraseMacroScopes
  unless n.isAtomic do
    throwErrorAt! binderView.id "invalid binder name '{n}', it must be atomic"

private partial def elabBinderViews {α} (binderViews : Array BinderView) (catchAutoBoundImplicit : Bool) (fvars : Array Expr) (k : Array Expr → TermElabM α)
    : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) : TermElabM α := do
    if h : i < binderViews.size then
      let binderView := binderViews.get ⟨i, h⟩
      ensureAtomicBinderName binderView
      if catchAutoBoundImplicit then
        elabTypeWithAutoBoundImplicit binderView.type fun type => do
          registerFailedToInferBinderTypeInfo type binderView.type
          withLocalDecl binderView.id.getId binderView.bi type fun fvar => do
            addLocalVarInfo binderView.id fvar
            loop (i+1) (fvars.push fvar)
      else
        let type ← elabType binderView.type
        registerFailedToInferBinderTypeInfo type binderView.type
        withLocalDecl binderView.id.getId binderView.bi type fun fvar => do
          addLocalVarInfo binderView.id fvar
          loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 fvars

private partial def elabBindersAux {α} (binders : Array Syntax) (catchAutoBoundImplicit : Bool) (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) : TermElabM α := do
    if h : i < binders.size then
      let binderViews ← matchBinder (binders.get ⟨i, h⟩)
      elabBinderViews binderViews catchAutoBoundImplicit fvars <| loop (i+1)
    else
      k fvars
  loop 0 #[]

/--
  Elaborate the given binders (i.e., `Syntax` objects for `simpleBinder <|> bracketedBinder`),
  update the local context, set of local instances, reset instance chache (if needed), and then
  execute `x` with the updated context. -/
def elabBinders {α} (binders : Array Syntax) (k : Array Expr → TermElabM α) (catchAutoBoundImplicit := false) : TermElabM α :=
  withoutPostponingUniverseConstraints do
    if binders.isEmpty then
      k #[]
    else
      elabBindersAux binders catchAutoBoundImplicit k

@[inline] def elabBinder {α} (binder : Syntax) (x : Expr → TermElabM α) (catchAutoBoundImplicit := false) : TermElabM α :=
  elabBinders #[binder] (catchAutoBoundImplicit := catchAutoBoundImplicit) (fun fvars => x (fvars.get! 0))

@[builtinTermElab «forall»] def elabForall : TermElab := fun stx _ =>
  match stx with
  | `(forall $binders*, $term) =>
    elabBinders binders fun xs => do
      let e ← elabType term
      mkForallFVars xs e
  | _ => throwUnsupportedSyntax

@[builtinTermElab arrow] def elabArrow : TermElab :=
  adaptExpander fun stx => match stx with
  | `($dom:term -> $rng) => `(forall (a : $dom), $rng)
  | _                    => throwUnsupportedSyntax

@[builtinTermElab depArrow] def elabDepArrow : TermElab := fun stx _ =>
  -- bracketedBinder `->` term
  let binder := stx[0]
  let term   := stx[2]
  elabBinders #[binder] fun xs => do
    mkForallFVars xs (← elabType term)

/--
  Auxiliary functions for converting `id_1 ... id_n` application into `#[id_1, ..., id_m]`
  It is used at `expandFunBinders`. -/
private partial def getFunBinderIds? (stx : Syntax) : OptionT TermElabM (Array Syntax) :=
  let convertElem (stx : Syntax) : OptionT TermElabM Syntax :=
    match stx with
    | `(_) => do let ident ← mkFreshIdent stx; pure ident
    | `($id:ident) => return id
    | _ => failure
  match stx with
  | `($f $args*) => do
     let mut acc := #[].push (← convertElem f)
     for arg in args do
       acc := acc.push (← convertElem arg)
     return acc
  | _ =>
    return #[].push (← convertElem stx)

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
      | Syntax.node `Lean.Parser.Term.simpleBinder _   => loop body (i+1) (newBinders.push binder)
      | Syntax.node `Lean.Parser.Term.hole _ =>
        let ident ← mkFreshIdent binder
        let type := binder
        loop body (i+1) (newBinders.push <| mkExplicitBinder ident type)
      | Syntax.node `Lean.Parser.Term.paren args =>
        -- `(` (termParser >> parenSpecial)? `)`
        -- parenSpecial := (tupleTail <|> typeAscription)?
        let binderBody := binder[1]
        if binderBody.isNone then
          processAsPattern ()
        else
          let idents  := binderBody[0]
          let special := binderBody[1]
          if special.isNone then
            processAsPattern ()
          else if special[0].getKind != `Lean.Parser.Term.typeAscription then
            processAsPattern ()
          else
            -- typeAscription := `:` term
            let type := special[0][1]
            match (← getFunBinderIds? idents) with
            | some idents => loop body (i+1) (newBinders ++ idents.map (fun ident => mkExplicitBinder ident type))
            | none        => processAsPattern ()
      | Syntax.ident .. =>
        let type  := mkHole binder
        loop body (i+1) (newBinders.push <| mkExplicitBinder binder type)
      | _ => processAsPattern ()
    else
      pure (newBinders, body, false)
  loop body 0 #[]

namespace FunBinders

structure State where
  fvars         : Array Expr := #[]
  lctx          : LocalContext
  localInsts    : LocalInstances
  expectedType? : Option Expr := none

private def propagateExpectedType (fvar : Expr) (fvarType : Expr) (s : State) : TermElabM State := do
  match s.expectedType? with
  | none              => pure s
  | some expectedType =>
    let expectedType ← whnfForall expectedType
    match expectedType with
    | Expr.forallE _ d b _ =>
      discard <| isDefEq fvarType d
      let b := b.instantiate1 fvar
      pure { s with expectedType? := some b }
    | _ => pure { s with expectedType? := none }

private partial def elabFunBinderViews (binderViews : Array BinderView) (i : Nat) (s : State) : TermElabM State := do
  if h : i < binderViews.size then
    let binderView := binderViews.get ⟨i, h⟩
    ensureAtomicBinderName binderView
    withRef binderView.type <| withLCtx s.lctx s.localInsts do
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
      addLocalVarInfoCore lctx binderView.id fvar
      let s ← withRef binderView.id <| propagateExpectedType fvar type s
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
    resettingSynthInstanceCacheWhen (s.localInsts.size > localInsts.size) <| withLCtx s.lctx s.localInsts <|
      x s.fvars s.expectedType?

/- Helper function for `expandEqnsIntoMatch` -/
private def getMatchAltsNumPatterns (matchAlts : Syntax) : Nat :=
  let alt0 := matchAlts[0][0]
  let pats := alt0[1].getSepArgs
  pats.size

def expandWhereDecls (whereDecls : Syntax) (body : Syntax) : MacroM Syntax :=
  match whereDecls with
  | `(whereDecls|where $[$decls:letRecDecl $[;]?]*) => `(let rec $decls:letRecDecl,*; $body)
  | _ => unreachable!

def expandWhereDeclsOpt (whereDeclsOpt : Syntax) (body : Syntax) : MacroM Syntax :=
  if whereDeclsOpt.isNone then
    body
  else
    expandWhereDecls whereDeclsOpt[0] body

/- Helper function for `expandMatchAltsIntoMatch` -/
private def expandMatchAltsIntoMatchAux (matchAlts : Syntax) (matchTactic : Bool) : Nat → Array Syntax → MacroM Syntax
  | 0,   discrs => do
    if matchTactic then
      `(tactic|match $[$discrs:term],* with $matchAlts:matchAlts)
    else
      `(match $[$discrs:term],* with $matchAlts:matchAlts)
  | n+1, discrs => withFreshMacroScope do
    let x ← `(x)
    let body ← expandMatchAltsIntoMatchAux matchAlts matchTactic n (discrs.push x)
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
    expands into (for tactic == false)
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
  withRef ref <| expandMatchAltsIntoMatchAux matchAlts tactic (getMatchAltsNumPatterns matchAlts) #[]

def expandMatchAltsIntoMatchTactic (ref : Syntax) (matchAlts : Syntax) : MacroM Syntax :=
  withRef ref <| expandMatchAltsIntoMatchAux matchAlts true (getMatchAltsNumPatterns matchAlts) #[]

/--
  Similar to `expandMatchAltsIntoMatch`, but supports an optional `where` clause.

  Expand `matchAltsWhereDecls` into `let rec` + `match`-expression.
  Example
    ```
    | 0, true => ... f 0 ...
    | i, _    => ... f i + g i ...
    where
      f x := g x + 1

      g : Nat → Nat
        | 0   => 1
        | x+1 => f x
    ```
    expands into
    ```
    fux x_1 x_2 =>
      let rec
        f x := g x + 1,
        g : Nat → Nat
          | 0   => 1
          | x+1 => f x
      match x_1, x_2 with
      | 0, true => ... f 0 ...
      | i, _    => ... f i + g i ...
    ```
-/
def expandMatchAltsWhereDecls (matchAltsWhereDecls : Syntax) : MacroM Syntax :=
  let matchAlts     := matchAltsWhereDecls[0]
  let whereDeclsOpt := matchAltsWhereDecls[1]
  let rec loop (i : Nat) (discrs : Array Syntax) : MacroM Syntax :=
    match i with
    | 0   => do
      let matchStx ← `(match $[$discrs:term],* with $matchAlts:matchAlts)
      if whereDeclsOpt.isNone then
        return matchStx
      else
        expandWhereDeclsOpt whereDeclsOpt matchStx
    | n+1 => withFreshMacroScope do
      let x ← `(x)
      let body ← loop n (discrs.push x)
      `(@fun $x => $body)
  loop (getMatchAltsNumPatterns matchAlts) #[]

@[builtinTermElab «fun»] partial def elabFun : TermElab :=
  fun stx expectedType? => loop stx expectedType?
where
  loop (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
    match stx with
    | `(fun $binders* => $body) => do
      let (binders, body, expandedPattern) ← expandFunBinders binders body
      if expandedPattern then
        let newStx ← `(fun $binders* => $body)
        loop newStx expectedType?
      else
        elabFunBinders binders expectedType? fun xs expectedType? => do
          /- We ensure the expectedType here since it will force coercions to be applied if needed.
             If we just use `elabTerm`, then we will need to a coercion `Coe (α → β) (α → δ)` whenever there is a coercion `Coe β δ`,
             and another instance for the dependent version. -/
          let e ← elabTermEnsuringType body expectedType?
          mkLambdaFVars xs e
    | `(fun $m:matchAlts) => do
      let stxNew ← liftMacroM $ expandMatchAltsIntoMatch stx m
      withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
    | _ => throwUnsupportedSyntax

/- If `useLetExpr` is true, then a kernel let-expression `let x : type := val; body` is created.
   Otherwise, we create a term of the form `(fun (x : type) => body) val`

   The default elaboration order is `binders`, `typeStx`, `valStx`, and `body`.
   If `elabBodyFirst == true`, then we use the order `binders`, `typeStx`, `body`, and `valStx`. -/
def elabLetDeclAux (id : Syntax) (binders : Array Syntax) (typeStx : Syntax) (valStx : Syntax) (body : Syntax)
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
  trace[Elab.let.decl] "{id.getId} : {type} := {val}"
  let result ←
    if useLetExpr then
      withLetDecl id.getId type val fun x => do
        addLocalVarInfo id x
        let body ← elabTerm body expectedType?
        let body ← instantiateMVars body
        mkLetFVars #[x] body
    else
      let f ← withLocalDecl id.getId BinderInfo.default type fun x => do
        addLocalVarInfo id x
        let body ← elabTerm body expectedType?
        let body ← instantiateMVars body
        mkLambdaFVars #[x] body
      pure <| mkApp f val
  if elabBodyFirst then
    forallBoundedTelescope type arity fun xs type => do
      let valResult ← elabTermEnsuringType valStx type
      let valResult ← mkLambdaFVars xs valResult
      unless (← isDefEq val valResult) do
        throwError "unexpected error when elaborating 'let'"
  pure result

structure LetIdDeclView where
  id      : Syntax
  binders : Array Syntax
  type    : Syntax
  value   : Syntax

def mkLetIdDeclView (letIdDecl : Syntax) : LetIdDeclView :=
  -- `letIdDecl` is of the form `ident >> many bracketedBinder >> optType >> " := " >> termParser
  let id      := letIdDecl[0]
  let binders := letIdDecl[1].getArgs
  let optType := letIdDecl[2]
  let type    := expandOptType letIdDecl optType
  let value   := letIdDecl[4]
  { id := id, binders := binders, type := type, value := value }

def expandLetEqnsDecl (letDecl : Syntax) : MacroM Syntax := do
  let ref       := letDecl
  let matchAlts := letDecl[3]
  let val ← expandMatchAltsIntoMatch ref matchAlts
  return Syntax.node `Lean.Parser.Term.letIdDecl #[letDecl[0], letDecl[1], letDecl[2], mkAtomFrom ref " := ", val]

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
      | true,  true  => stxNew.setKind `Lean.Parser.Term.«let*»
      | false, true  => stxNew.setKind `Lean.Parser.Term.«let!»
      | false, false => unreachable!
    withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  else if letDecl.getKind == `Lean.Parser.Term.letEqnsDecl then
    let letDeclIdNew ← liftMacroM <| expandLetEqnsDecl letDecl
    let declNew := stx[1].setArg 0 letDeclIdNew
    let stxNew  := stx.setArg 1 declNew
    withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
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

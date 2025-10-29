import Lean
import Lean.Elab.Tactic.Do.LetElim
import Std.Tactic.Do
import Init.Control.OptionCps
import Init.Control.StateCps

open Lean Parser Meta Elab

#reduce (types := true) StateT Bool (ExceptCpsT Nat Id) Nat
#reduce (types := true) OptionCpsT (StateT Bool Id) Nat
#reduce (types := true) OptionCpsT (StateCpsT Bool Id) Nat
#reduce (types := true) Nat → OptionCpsT Id PUnit

def OptionT.runK [Monad m] (x : OptionT m α) (ok : α → m β) (error : Unit → m β) : m β :=
  x.run >>= (·.casesOn (error ()) ok)

def ExceptT.runK [Monad m] (x : ExceptT ε m α) (ok : α → m β) (error : ε → m β) : m β :=
  x.run >>= (·.casesOn error ok)

def ExceptT.runCatch [Monad m] (x : ExceptT α m α) : m α :=
  x.runK pure pure

abbrev EarlyReturnT := ExceptT
abbrev EarlyReturnT.return {m : Type w → Type x} [Monad m] : ρ → EarlyReturnT ρ m α := throw

abbrev BreakT := OptionT
abbrev BreakT.break {m : Type w → Type x} [Monad m] : BreakT (StateT σ (EarlyReturnT ρ m)) PUnit := throw ()
abbrev BreakT.continue {m : Type w → Type x} [Monad m] : BreakT (StateT σ (EarlyReturnT ρ m)) PUnit := pure ⟨⟩

class Foldable (ρ : Type u) (α : outParam (Type v)) extends Membership α ρ where
  foldr {β : Type w} : (α → β → β) → β → ρ → β
  foldrMem {β : Type w} : (xs : ρ) → ((a : α) → a ∈ xs → β → β) → β → β
  foldl {β : Type w} : (β → α → β) → β → ρ → β
  foldlMem {β : Type w} : (xs : ρ) → (β → (a : α) → a ∈ xs → β) → β → β
  length : ρ → Nat

@[specialize 3 4] def List.foldrNonTR (f : α → β → β) (init : β) : (l : List α) → β
  | []     => init
  | a :: l => f a (foldrNonTR f init l)

instance : Foldable (List α) α where
  foldr := List.foldrNonTR
  foldl := List.foldl
  foldlMem xs f z := List.foldl (fun b ⟨a, h⟩ => f b a h) z xs.attach
  foldrMem xs f z := List.foldr (fun ⟨a, h⟩ b => f a h b) z xs.attach
  length := List.length

instance : Foldable (Array α) α where
  foldr := Array.foldr
  foldl := Array.foldl
  foldlMem xs f z := Array.foldl (fun b ⟨a, h⟩ => f b a h) z xs.attach
  foldrMem xs f z := Array.foldr (fun ⟨a, h⟩ b => f a h b) z xs.attach
  length := Array.size

@[specialize]
def Foldable.toList [Foldable ρ α] : ρ → List α :=
  foldr (fun a acc => a :: acc) []

@[specialize]
def Foldable.foldl' [Foldable ρ α] (f : β → α → β) (init : β) (xs : ρ) : β :=
  foldr (fun a k b => k (f b a)) id xs init

set_option trace.Compiler.saveBase true in
example := Foldable.foldl' (fun a b => a * b) 1 [1, 2, 3]

class LawfulFoldable (ρ : Type u) (α : outParam (Type v)) [Foldable ρ α] : Prop where
  -- Unsure whether the following law follows by parametricity.
  foldr_eq_foldr_toList (xs : ρ) (k : α → β → β) (z : β) :
    Foldable.foldr k z xs = List.foldr k z (Foldable.toList xs)

@[specialize]
def Foldable.toArray [Foldable ρ α] (xs : ρ) : Array α :=
  foldr (fun a k arr => k (arr.push a)) id xs (Array.mkEmpty (Foldable.length xs))

@[specialize 4 5]
def Foldable.foldrTR [Foldable ρ α] (f : α → β → β) (init : β) (xs : ρ) : β :=
  xs |> Foldable.toArray |>.foldr f init

-- def warmup := Foldable.toArray [3]
-- set_option trace.Compiler.saveBase true in
-- def blah := Foldable.foldrTR (fun a b => a * b) 0 [1, 2, 3]
-- set_option trace.Compiler.saveBase true in
-- example := List.foldr (fun a b => a * b) 0 [1, 2, 3]

@[inline]
def Foldable.forBreak_ {ρ : Type u} {α : Type v} [Foldable ρ α] {m : Type w → Type x} [Monad m] {σ ε γ} (xs : ρ) (s : σ) (body : α → BreakT (StateT σ (EarlyReturnT ε m)) PUnit) (kreturn : ε → m γ) (kbreak : σ → m γ) : m γ :=
  Foldable.foldr
    (fun a acc s => do
      let e ← body a s
      match e with
      | .error r => kreturn r
      | .ok (.some _, s) => acc s
      | .ok (none, s) => kbreak s)
    kbreak
    xs
    s

declare_syntax_cat dooElem

meta def dooElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `dooElem rbp

meta def dooSeqItem      := leading_parser
  ppLine >> dooElemParser >> optional "; "
meta def dooSeqIndent    := leading_parser
  many1Indent dooSeqItem
meta def dooSeqBracketed := leading_parser
  "{" >> withoutPosition (many1 dooSeqItem) >> ppLine >> "}"
meta def dooSeq :=
  withAntiquot (mkAntiquot "dooSeq" decl_name% (isPseudoKind := true)) <|
    dooSeqBracketed <|> dooSeqIndent
meta def dooIdDecl := leading_parser
  atomic (ident >> Term.optType >> ppSpace >> Term.leftArrow) >>
  dooElemParser
syntax:arg (name := dooBlock) "doo" dooSeq : term

syntax (name := dooTerm) Term.doExpr : dooElem
syntax (name := dooParens) "(" dooSeq ")" : dooElem
syntax (name := dooReturn) &"return " term : dooElem
syntax (name := dooBreak) &"break" : dooElem
syntax (name := dooContinue) &"continue" : dooElem
syntax (name := dooLet) "let " &"mut "? letDecl : dooElem
syntax (name := dooLetArrow) "let " &"mut "? dooIdDecl : dooElem
syntax (name := dooNested) "doo" dooSeq : dooElem
meta def dooForDecl := leading_parser
  termParser >> " in " >> withForbidden "doo" termParser
syntax (name := dooFor) "for " dooForDecl,+ "doo " dooSeq : dooElem

@[dooElem_parser]
meta def dooReassign      := leading_parser
  Term.notFollowedByRedefinedTermToken >> Term.letIdDeclNoBinders

@[dooElem_parser]
meta def dooReassignArrow := leading_parser
  Term.notFollowedByRedefinedTermToken >> dooIdDecl

@[dooElem_parser]
meta def dooIf := leading_parser withResetCache <| withPositionAfterLinebreak <| ppRealGroup <|
  -- ppRealFill (ppIndent ("if " >> doIfCond >> " then") >> ppSpace >> doSeq) >>
  ppRealFill (ppIndent ("if " >> termParser >> " then") >> ppSpace >> dooSeq) >>
  many (checkColGe "'else if' in 'do' must be indented" >>
    -- group (ppDedent ppSpace >> ppRealFill (elseIf >> doIfCond >> " then " >> doSeq))) >>
    group (ppDedent ppSpace >> ppRealFill (Term.elseIf >> termParser >> " then " >> dooSeq))) >>
  optional (checkColGe "'else' in 'do' must be indented" >>
    ppDedent ppSpace >> ppRealFill ("else " >> dooSeq))

meta def getDooElems (dooSeq : TSyntax `dooSeq) : Array (TSyntax `dooElem) :=
  if dooSeq.raw.getKind == ``dooSeqBracketed then
    dooSeq.raw[1].getArgs.map fun arg => ⟨arg[0]⟩
  else if dooSeq.raw.getKind == ``dooSeqIndent then
    dooSeq.raw[0].getArgs.map fun arg => ⟨arg[0]⟩
  else
    #[]

namespace Do

structure MonadInfo where
  /-- The inferred type of the monad of type `Type u → Type v`. -/
  m : Expr
  /-- The `u` in `m : Type u → Type v`. -/
  u : Level
  /-- The `v` in `m : Type u → Type v`. -/
  v : Level
  /-- The cached `PUnit` expression. -/
  cachedPUnit : Expr :=
    if u matches .zero then mkConst ``Unit else mkConst ``PUnit [mkLevelSucc u]
  /-- The cached `PUnit.unit` expression. -/
  cachedPUnitUnit : Expr :=
    if u matches .zero then mkConst ``Unit.unit else mkConst ``PUnit.unit [mkLevelSucc u]

private meta partial def extractBind (expectedType? : Option Expr) : TermElabM (MonadInfo × Expr) := do
  let some expectedType := expectedType? | mkUnknownMonadResult
  let extractStep? (type : Expr) : TermElabM (Option (MonadInfo × Expr)) := do
    let .app m resultType := type.consumeMData | return none
    unless ← isType resultType do return none
    let .succ u ← getLevel resultType | return none
    let .succ v ← getLevel type | return none
    let u := u.normalize
    let v := v.normalize
    return some ({ m, u, v }, resultType)
  let rec extract? (type : Expr) : TermElabM (Option (MonadInfo × Expr)) := do
    match (← extractStep? type) with
    | some r => return r
    | none =>
      let typeNew ← whnfCore type
      if typeNew != type then
        extract? typeNew
      else
        -- Term.tryPostponeIfMVar typeNew.getAppFn
        if typeNew.getAppFn.isMVar then
          mkUnknownMonadResult
        else match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
  match (← extract? expectedType) with
  | some r => return r
  | none   => throwError "invalid `do` notation, expected type is not a monad application{indentExpr expectedType}\nYou can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad."
where
  mkUnknownMonadResult : TermElabM (MonadInfo × Expr) := do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let m ← mkFreshExprMVar (← mkArrow (mkSort (mkLevelSucc u)) (mkSort (mkLevelSucc v))) (userName := `m)
    let resultType ← mkFreshExprMVar (mkSort (mkLevelSucc u)) (userName := `α)
    return ({ m, u, v }, resultType)

-- Same pattern as for `Methods`/`MethodsRef` in `SimpM`.
private opaque ContInfoRefPointed : NonemptyType.{0}

def ContInfoRef : Type := ContInfoRefPointed.type

instance : Nonempty ContInfoRef :=
  by exact ContInfoRefPointed.property

structure Context where
  /-- Inferred and cached information about the monad. -/
  monadInfo : MonadInfo
  /-- The mutable variables in declaration order. -/
  mutVars : Array Name := #[]
  /-- The expected type of `e` in `return e`. -/
  earlyReturnType : Expr
  /--
  The expected type of the current `do` block.
  This can be different from `earlyReturnType` in `for` loop `do` blocks, for example.
  -/
  doBlockResultType : Expr
  -- /-- The continuation for an early `return`. -/
  -- returnCont : ContInfo
  --/--
  --The success continuation of type `α → m α` for expected result type `α` for regular exit of
  --the `do` sequence.
  ---/
  --successCont : Expr → Expr
  contInfo : ContInfoRef

structure MonadInstanceCache where
  /-- The inferred `Pure` instance of `(← read).monadInfo.m`. -/
  instPure : Option Expr := none
  /-- The inferred `Bind` instance of `(← read).monadInfo.m`. -/
  instBind : Option Expr := none
  /-- The cached `Pure.pure` expression. -/
  cachedPure : Option Expr := none
  /-- The cached `Bind.bind` expression. -/
  cachedBind : Option Expr := none

/--
A continuation metavariable.

When generating jumps to join points or filling in expressions for `break` or `continue`, it is
still unclear what mutable variables need to be passed, because it depends on which mutable
variables were reassigned in the control flow path to *any* of the jumps.

The mechanism of `ContVarId` allows to delay the assignment of the jump expressions until the local
contexts of all the jumps are known.
-/
structure ContVarId where
  name : Name
  deriving Inhabited, BEq, Hashable

/--
Information about a jump site associated to `ContVarId`.
There will be one instance per jump site to a join point, or for each `break` or `continue`
element.
-/
structure ContVarJump where
  /--
  The metavariable to be assigned with the jump to the join point.
  Conveniently, its captured local context is that of the jump, in which the new mutable variable
  definitions and result variable are in scope.
  -/
  mvar : Expr
  /-- A reference for error reporting. -/
  ref : Syntax

/--
Information about a `ContVarId`.
-/
structure ContVarInfo where
  /-- The monadic type of the continuation. -/
  type : Expr
  /-- The tracked jumps to the continuation. Each contains a metavariable to be assigned later. -/
  jumps : Array ContVarJump

structure State where
  monadInstanceCache : MonadInstanceCache := {}
  contVars : Std.HashMap ContVarId ContVarInfo := {}

abbrev DoElabM := ReaderT Context <| StateRefT State TermElabM

/--
Information about a success, `return`, `break` or `continue` continuation that will be filled in
after the code using it has been elaborated.
-/
structure ContInfo where
  returnCont : Expr → DoElabM Expr
  breakCont : Option (DoElabM Expr) := none
  continueCont : Option (DoElabM Expr) := none
deriving Inhabited

unsafe def ContInfo.toContInfoRefImpl (m : ContInfo) : ContInfoRef :=
  unsafeCast m

@[implemented_by ContInfo.toContInfoRefImpl]
opaque ContInfo.toContInfoRef (m : ContInfo) : ContInfoRef

unsafe def ContInfoRef.toContInfoImpl (m : ContInfoRef) : ContInfo :=
  unsafeCast m

@[implemented_by ContInfoRef.toContInfoImpl]
opaque ContInfoRef.toContInfo (m : ContInfoRef) : ContInfo

meta def mkMonadicType (resultType : Expr) : DoElabM Expr := do
  return mkApp (← read).monadInfo.m resultType

meta def mkPUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnit

meta def mkPUnitUnit : DoElabM Expr := do
  return (← read).monadInfo.cachedPUnitUnit

meta def getCachedPure : DoElabM Expr := do
  let s ← get
  if let some cachedPure := s.monadInstanceCache.cachedPure then return cachedPure
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Pure [info.u, info.v]) info.m)
  let cachedPure := mkApp2 (mkConst ``Pure.pure [info.u, info.v]) info.m instPure
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedPure := some cachedPure } : State}
  return cachedPure

meta def mkPureApp (ref : Syntax) (α e : Expr) : DoElabM Expr := withRef ref do
  let e ← Term.ensureHasType α e
  return mkApp2 (← getCachedPure) α e

meta def mkContext (expectedType? : Option Expr) : TermElabM Context := do
  let (mi, resultType) ← extractBind expectedType?
  let returnCont e := do mkPureApp (← getRef) resultType e
  let contInfo := ContInfo.toContInfoRef { returnCont }
  return { monadInfo := mi, earlyReturnType := resultType, doBlockResultType := resultType, contInfo }

meta def mkBindApp (ref : Syntax) (α β e k : Expr) : DoElabM Expr := withRef ref do
  let mα ← mkMonadicType α
  let e ← Term.ensureHasType mα e
  let k ← Term.ensureHasType (← mkArrow α (← mkMonadicType β)) k
  let s ← get
  if let some cachedBind := s.monadInstanceCache.cachedBind then return mkApp4 cachedBind α β e k
  let info := (← read).monadInfo
  let instPure ← Term.mkInstMVar (mkApp (mkConst ``Bind [info.u, info.v]) info.m)
  let cachedBind := mkApp2 (mkConst ``Bind.bind [info.u, info.v]) info.m instPure
  set { s with monadInstanceCache := { s.monadInstanceCache with cachedBind := some cachedBind } : State}
  return mkApp4 cachedBind α β e k

meta def withNewMonad (u v : Level) (m : Expr) (x : DoElabM α) : DoElabM α := do
  let s ← get
  set { : State }
  let r ← withReader (fun ctx => { ctx with monadInfo := { m := m, u := u, v := v } }) x
  set s
  return r

meta def declareMutVar (x : Name) : DoElabM α → DoElabM α :=
  withReader fun ctx => { ctx with mutVars := ctx.mutVars.push x }

meta def declareMutVar? (mutTk? : Option Syntax) (x : Name) (k : DoElabM α) : DoElabM α :=
  if mutTk?.isSome then declareMutVar x k else k

meta def throwUnlessMutVarDeclared (ref : Syntax) (x : Name) : DoElabM Unit := do
  unless (← read).mutVars.contains x do
    throwErrorAt ref "mutable variable `{x}` is not declared"

meta def checkMutVarsForShadowing (ref : Syntax) (x : Name) : DoElabM Unit := do
  if (← read).mutVars.contains x then
    throwErrorAt ref "mutable variable `{x.simpMacroScopes}` cannot be shadowed"

meta def mkLetThen (x : Name) (ty : Expr) (rhs : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  withLetDecl x ty rhs fun x => do
    let e ← k x
    -- logInfo m!"before mkLetFVars {x}: {e}"
    let e ← mkLetFVars (usedLetOnly := false) #[x] e
    -- logInfo m!"after mkLetFVars {x}: {e}"
    return e

meta def mkFreshResultType : DoElabM Expr := do
  mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := `α)

meta def mkBind (ref : Syntax) (x : Name) (eResultTy e : Expr) (k : Expr → DoElabM Expr) : DoElabM Expr := do
  let (k, kResultTy) ← withLocalDeclD x eResultTy fun x => do
    let body ← k x
    let bodyTy ← inferType body
    let .app _m kResultTy := bodyTy
      | throwError "Expected some monadic type for{indentExpr body}\nbut got{indentExpr bodyTy}"
    return (← mkLambdaFVars #[x] body, kResultTy)
  mkBindApp ref eResultTy kResultTy e k

meta def mkPureUnit (ref : Syntax) : DoElabM Expr := do
  mkPureApp ref (← mkPUnit) (← mkPUnitUnit)

/--
A variant of `Term.elabType` that takes the universe of the monad into account, unless
`freshLevel` is set.
-/
meta def elabType (ty? : Option (TSyntax `term)) (freshLevel := false) : DoElabM Expr := do
  let u ← if freshLevel then mkFreshLevelMVar else (mkLevelSucc ·.monadInfo.u) <$> read
  let sort := mkSort u
  match ty? with
  | none => mkFreshExprMVar sort
  | some ty => Term.elabTermEnsuringType ty sort

meta def filterReassigned (mutVars : Array Name) (oldCtx newCtx : LocalContext) : Array Name :=
  let oldDefs := mutVars.map oldCtx.findFromUserName?
  let newDefs := mutVars.map newCtx.findFromUserName?
  oldDefs.zip newDefs
    -- this filters out names that are defined in newCtx but not in oldCtx
    |>.filterMap (fun (old, new) => (·, ·) <$> old <*> new)
    |>.filter (Function.uncurry (·.toExpr != ·.toExpr))
    |>.map (·.1.userName)

meta def getReassignedMutVars (rootCtx : LocalContext) (childCtxs : Array LocalContext) : DoElabM (Array Name) := do
  let mutVars := (← read).mutVars
  let mut reassignedMutVars := Std.HashSet.emptyWithCapacity mutVars.size
  for childCtx in childCtxs do
    reassignedMutVars := reassignedMutVars.insertMany (filterReassigned mutVars rootCtx childCtx)
  return mutVars.filter reassignedMutVars.contains

meta def mkFreshContVar (resultType : Expr) : DoElabM ContVarId := do
  let name ← mkFreshId
  let contVarId := ContVarId.mk name
  let type ← mkMonadicType resultType
  modify fun s => { s with contVars := s.contVars.insert contVarId { type, jumps := #[] } }
  return contVarId

meta def ContVarId.find (contVarId : ContVarId) : DoElabM ContVarInfo := do
  match (← get).contVars.get? contVarId with
  | some info => return info
  | none => throwError "contVarId {contVarId.name} not found"

meta def ContVarId.mkJump (contVarId : ContVarId) : DoElabM Expr := do
  let info ← contVarId.find
  let mvar ← mkFreshExprMVar info.type
  let jumps := info.jumps.push { mvar, ref := (← getRef) }
  modify fun s => { s with contVars := s.contVars.insert contVarId { info with jumps } }
  return mvar

meta def ContVarId.jumpCount (contVarId : ContVarId) : DoElabM Nat := do
  let info ← contVarId.find
  return info.jumps.size

meta def ContVarId.synthesizeJumps (contVarId : ContVarId) (k : DoElabM Expr) : DoElabM Unit := do
  let info ← contVarId.find
  for jump in info.jumps do
    jump.mvar.mvarId!.withContext do withRef jump.ref do
      let res ← k
      discard <| isDefEq jump.mvar res

meta def ContVarId.erase (contVarId : ContVarId) : DoElabM Unit := do
  modify fun s => { s with contVars := s.contVars.erase contVarId }

meta def ContVarId.getReassignedMutVars (contVarId : ContVarId) (rootCtx : LocalContext) : DoElabM (Array Name) := do
  let info ← contVarId.find
  let mvarDecls ← info.jumps.mapM (·.mvar.mvarId!.getDecl)
  Do.getReassignedMutVars rootCtx (mvarDecls.map (·.lctx))

/--
This data type communicates to `do` element elaborators whether they are the last element of the
`do` block and what is the expected monadic result type. When it's not the last element, there's a
continuation for elaborating the remaining `do` elements of the block.

Every `do` element has a notion of "result", which can be given a name with monadic bind.
Clearly, for expression elements `e : m α`, the result has type `α`.
More subtly, for binding elements `let x := e` or `let x ← e`, the result has type `PUnit` and is
unrelated to the type of any bound variable `x`.
-/
inductive DoElemCont where
  /--
  The `do` element under elaboration is the last of its `do` block and has the given result type.
  The elaborator must generate a closed expression for this monadic result type.
  For example, `let x ← e` elaborates to `e >>= fun x => pure ()`.
  -/
  | last : (resultType : Expr) → DoElemCont

  /--
  The `do` element under elaboration is followed by other elements in the `do` block,
  and they can be elaborated using `k`. `k` expects that the result of the previous `do` element
  has type `resultType` and can be found in the local context under user name `resultName`.

  Examples:
  * `return` drops the continuation; `return x; pure ()` elaborates to `pure x`.
  * `let x ← e; rest x` elaborates to `e >>= fun x => rest x`.
  * `let x := 3; let y ← (let x ← e); rest x` elaborates to
    `let x := 3; e >>= fun x_1 => let y := (); rest x`, which is immediately zeta-reduced to
    `let x := 3; e >>= fun x_1 => rest x`.
  * `one; two` elaborates to `one >>= fun (_ : PUnit) => two`; it is an error if `one` does not have
    type `PUnit`.
  -/
  | cont : (resultName : Name) → (resultType : Expr) → (k : DoElabM Expr) → DoElemCont

meta def DoElemCont.resultType (k : DoElemCont) : Expr :=
  match k with
  | .last resultType => resultType
  | .cont _ resultType _ => resultType

meta def DoElemCont.mkBindUnlessLast (ref : Syntax) (k : DoElemCont) (e : Expr) : DoElabM Expr :=
  if let .cont resultName resultType k := k then do
    mkBind ref resultName resultType e (fun _ => k)
  else
    return e

meta def withInlinedLetDecl (name : Name) (type rhs : Expr) (k : DoElabM Expr) : DoElabM Expr := do
  withLetDecl name type rhs fun x => do
    let e ← k
    let e ← elimMVarDeps #[x] e
    return e.replaceFVar x rhs

meta def DoElemCont.continueWithUnit (ref : Syntax) (k : DoElemCont) : DoElabM Expr := withRef ref do
  let unit ← mkPUnitUnit
  discard <| Term.ensureHasType k.resultType unit
  match k with
  | .cont n _ k => do withInlinedLetDecl n (← mkPUnit) unit k
  | .last _ => mkPureUnit ref

meta def captureLCtxAndMutVarDefs (k : (Name → DoElabM Expr → DoElabM Expr) → DoElabM Expr) : DoElabM Expr := do
  let mutVars := (← read).mutVars
  let lctx ← getLCtx
  k <| fun r k => do
    -- Find the subset of mut vars that are reassigned.
    let reassignedMutVars := filterReassigned mutVars lctx (← getLCtx)
    let reassignedMutVarDefs ← reassignedMutVars.mapM (getFVarFromUserName ·)
    -- Tunnel mut vars and result into the outer context:
    let tunnelDecls ← reassignedMutVarDefs
      |>.push (← getFVarFromUserName r)
      |>.mapM (·.fvarId!.getDecl)
    -- Forget the value of every ldecl.
    let tunnelDecls := tunnelDecls.map fun decl =>
      .cdecl 0 decl.fvarId decl.userName decl.type decl.binderInfo decl.kind
    withLCtx' lctx do
    withExistingLocalDecls tunnelDecls.toList do
    withReader (fun ctx => { ctx with mutVars }) do
    k

meta def DoElemCont.withDuplicableCont (dec : DoElemCont) (caller : DoElemCont → DoElabM Expr) : DoElabM Expr := do
  let .cont rName resultType nondupK := dec | caller dec -- assumption: .last continuations are always duplicable
  let α := (← read).doBlockResultType
  let mα ← mkMonadicType α
  let joinTy ← mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.v)) (userName := `joinTy)
  let joinRhs ← mkFreshExprMVar joinTy (userName := `joinRhs)
  withLetDecl (← mkFreshUserName `__do_jp) joinTy joinRhs (kind := .implDetail) fun jp => do
  captureLCtxAndMutVarDefs fun restoreLCtx => do
    let contVarId ← mkFreshContVar α
    let duplicableDec := DoElemCont.cont rName resultType (restoreLCtx rName (contVarId.mkJump))
    let e ← caller duplicableDec

    -- Now determine whether we need to realize the join point.
    let jumpCount ← contVarId.jumpCount
    if jumpCount = 0 then
      -- Do nothing. No MVar needs to be assigned.
      pure ()
    else if jumpCount = 1 then
      -- Linear use of the continuation. Do not introduce a join point; just emit the continuation
      -- directly.
      contVarId.synthesizeJumps nondupK
    else -- jumps.size > 1
      -- Non-linear use of the continuation. Introduce a join point and synthesize jumps to it.

      -- Compute the union of all reassigned mut vars. These + `r` constitute the parameters
      -- of the join point. We take a little care to preserve the declaration order that is manifest
      -- in the array `(← read).mutVars`.
      let reassignedMutVars ← contVarId.getReassignedMutVars (← joinRhs.mvarId!.getDecl).lctx

      -- Assign the `joinTy` based on the types of the reassigned mut vars and the result type.
      let reassignedDecls ← reassignedMutVars.mapM (getLocalDeclFromUserName ·)
      let reassignedTys := reassignedDecls.map (·.type)
      let resTy ← mkFreshExprMVar (mkSort (mkLevelSucc (← read).monadInfo.u)) (userName := `resTy)
      discard <| isDefEq joinTy (← mkArrowN (reassignedTys.push resTy) mα)

      -- Assign the `joinRhs` with the result of the continuation.
      let rhs ← joinRhs.mvarId!.withContext do
        withLocalDeclsDND (reassignedDecls.map (fun d => (d.userName, d.type)) |>.push (rName, resTy)) fun xs => do
          mkLambdaFVars xs (← nondupK)
      discard <| isDefEq joinRhs rhs

      -- Finally, assign the MVars with the jump to `jp`.
      contVarId.synthesizeJumps do
        let r ← getFVarFromUserName rName
        let mut jump := jp
        for name in reassignedMutVars do
          let newDefn ← getLocalDeclFromUserName name
          jump := mkApp jump newDefn.toExpr
        return mkApp jump (← Term.ensureHasType resTy r "Mismatched result type for match arm. It")

    mkLetFVars #[jp] (usedLetOnly := true) (← Term.ensureHasType mα e)

/-- Given expressions `eᵢ`, return the tuple `(e₁, e₂, …, eₙ)` and its type `t₁ × t₂ × … × tₙ`. -/
meta def mkProdMkN (es : Array Expr) : MetaM (Expr × Expr) := do
  if h : es.size > 0 then
    let mut tuple := es.back
    let mut tupleTy ← inferType tuple
    let mut u ← getDecLevel tupleTy
    let mut es := es.pop
    for i in 0...es.size do
      let ty ← inferType es[es.size - i - 1]!
      let u' ← getDecLevel ty
      tuple := mkApp4 (mkConst ``Prod.mk [u', u]) ty tupleTy es[es.size - i - 1]! tuple
      tupleTy := mkApp2 (mkConst ``Prod [u', u]) ty tupleTy
      u := (mkLevelMax u u').normalize
      es := es.pop
    return (tuple, tupleTy)
  else
    let u ← mkFreshLevelMVar
    return (mkConst ``PUnit.unit [u], mkConst ``PUnit [u])

meta def getProdFields (tuple tupleTy : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let tupleTy ← instantiateMVarsIfMVarApp tupleTy
  let_expr c@Prod fstTy sndTy := tupleTy
    | throwError "Internal error: Expected Prod, got {tuple} of type {tupleTy}"
  let fst := mkApp3 (mkConst ``Prod.fst c.constLevels!) fstTy sndTy tuple
  let snd := mkApp3 (mkConst ``Prod.snd c.constLevels!) fstTy sndTy tuple
  return (fst, fstTy, snd, sndTy)

meta def bindMutVarsFromTuple (vars : List Name) (tupleVar : FVarId) (k : DoElabM Expr) : DoElabM Expr :=
  do go vars tupleVar (← tupleVar.getType) #[]
where
  go vars tupleVar tupleTy letFVars := do
    let tuple := mkFVar tupleVar
    match vars with
    | []  => mkLetFVars letFVars (← k)
    | [x] =>
      withLetDecl x tupleTy tuple fun x => do mkLetFVars (letFVars.push x) (← k)
    | [x, y] =>
      let (fst, fstTy, snd, sndTy) ← getProdFields tuple tupleTy
      withLetDecl x fstTy fst fun x =>
      withLetDecl y sndTy snd fun y => do mkLetFVars (letFVars.push x |>.push y) (← k)
    | x :: xs => do
      let (fst, fstTy, snd, sndTy) ← getProdFields tuple tupleTy
      withLetDecl x fstTy fst fun x => do
      withLetDecl (← tupleVar.getUserName) sndTy snd fun r => do
        go xs r.fvarId! sndTy (letFVars |>.push x |>.push r)

meta def enterLoopBody (resultType : Expr) (returnCont : Expr → DoElabM Expr) (breakCont continueCont : DoElabM Expr) : (body : DoElabM Expr) → DoElabM Expr :=
  let contInfo := ContInfo.toContInfoRef { breakCont, continueCont, returnCont }
  withReader fun ctx => { ctx with contInfo, doBlockResultType := resultType }

meta def withProxyMutVarDefs [Inhabited α] (k : (Expr → DoElabM Expr) → DoElabM α) : DoElabM α := do
  let mutVars := (← read).mutVars
  let outerCtx ← getLCtx
  let outerDecls := mutVars.map outerCtx.getFromUserName!
  withLocalDeclsDND (← outerDecls.mapM fun x => do return (x.userName, x.type)) fun proxyDefs => do
    let proxyCtx ← getLCtx
    let elimProxyDefs e : DoElabM Expr := do
      let innerCtx ← getLCtx
      let actualDefs := proxyDefs.map fun pDef =>
        let x := (proxyCtx.getFVar! pDef).userName
        let iDef := (innerCtx.getFromUserName! x).toExpr
        if iDef == pDef then
          (outerCtx.getFromUserName! x).toExpr  -- original definition
        else
          iDef                                  -- reassigned definition
      let e ← elimMVarDeps proxyDefs e
      return e.replaceFVars proxyDefs actualDefs
    k elimProxyDefs

meta def getReturnCont : DoElabM (Expr → DoElabM Expr) := do
  return (← read).contInfo.toContInfo.returnCont

meta def getBreakCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.breakCont

meta def getContinueCont : DoElabM (Option (DoElabM Expr)) := do
  return (← read).contInfo.toContInfo.continueCont

mutual
  meta def elabElem (dooElem : TSyntax `dooElem) (k : DoElemCont) : DoElabM Expr := withRef dooElem do
    match dooElem with
    -- First off the three constructs that discard the continuation `k`:
    | `(dooElem| return $e) =>
      let e ← Term.elabTermEnsuringType e (← read).earlyReturnType
      let returnCont ← getReturnCont
      returnCont e
    | `(dooElem| break) =>
      let some breakCont := (← getBreakCont)
        | throwError "`break` must be nested inside a loop"
      breakCont
      -- NB: discard continuation `k?`, unconditionally
    | `(dooElem| continue) =>
      let some continueCont := (← getContinueCont)
        | throwError "`continue` must be nested inside a loop"
      continueCont
    | `(dooElem| $e:term) =>
      let mα ← mkMonadicType k.resultType
      let e ← Term.elabTermEnsuringType e mα
      k.mkBindUnlessLast dooElem e
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? ← $rhs) =>
      checkMutVarsForShadowing dooElem x.getId
      let xType ← elabType xType?
      captureLCtxAndMutVarDefs fun restoreLCtx =>
        elabElem rhs <| .cont x.getId xType do
          restoreLCtx x.getId do
            declareMutVar? mutTk? x.getId (k.continueWithUnit x)
    | `(dooElem| $x:ident ← $rhs) =>
      let xType := (← getLocalDeclFromUserName x.getId).type
      captureLCtxAndMutVarDefs fun restoreLCtx =>
        elabElem rhs <| .cont x.getId xType do
          restoreLCtx x.getId do
            k.continueWithUnit x
    | `(dooElem| let $[mut%$mutTk?]? $x:ident $[: $xType?]? := $rhs) =>
      checkMutVarsForShadowing dooElem x.getId
      -- We want to allow `do let foo : Nat = Nat := rfl; pure (foo ▸ 23)`. Note that the type of
      -- foo has sort `Sort 0`, whereas the sort of the monadic result type `Nat` is `Sort 1`.
      -- Hence `freshLevel := true` (yes, even for `mut` vars; why not?).
      let xType ← elabType xType? (freshLevel := true)
      let rhs ← Term.elabTermEnsuringType rhs xType
      mkLetThen x.getId xType rhs fun _xdefn => declareMutVar? mutTk? x.getId (k.continueWithUnit x)
    | `(dooElem| $x:ident := $rhs) =>
      let xType := (← getLocalDeclFromUserName x.getId).type
      let rhs ← Term.elabTermEnsuringType rhs xType
      mkLetThen x.getId xType rhs fun _xdefn => k.continueWithUnit x
    | `(dooElem| if $cond then $thenDooSeq $[else $elseDooSeq?]?) =>
      k.withDuplicableCont fun k => do
        let then_ ← elabElems1 (getDooElems thenDooSeq) k
        let else_ ← match elseDooSeq? with
          | none => k.continueWithUnit dooElem
          | some elseDooSeq => elabElems1 (getDooElems elseDooSeq) k
        let then_ ← Term.exprToSyntax then_
        let else_ ← Term.exprToSyntax else_
        Term.elabTerm (← `(if $cond then $then_ else $else_)) none
    | `(dooElem| doo $dooSeq) => elabElems1 (getDooElems dooSeq) k
    | `(dooElem| for $x:ident in $xs doo $dooSeq) =>
      -- set_option pp.universes true in #print forBreakMem_
      let uα ← mkFreshLevelMVar
      let uρ ← mkFreshLevelMVar
      let α ← mkFreshExprMVar (mkSort (mkLevelSucc uα)) (userName := `α)
      let ρ ← mkFreshExprMVar (mkSort (mkLevelSucc uρ)) (userName := `ρ)
      let xs ← Term.elabTermEnsuringType xs ρ
      let mi := (← read).monadInfo
      let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
      let σ ← mkFreshExprMVar (mkSort (mkLevelSucc mi.u)) (userName := `σ)
      let preS ← mkFreshExprMVar σ (userName := `s)
      let ε := (← read).earlyReturnType
      let γ := (← read).doBlockResultType
      let (body, reassignedMutVars) ←
        withLocalDeclD x.getId α fun x => do
        withLocalDeclD (← mkFreshUserName `s) σ fun loopS => do
          -- result type is
          -- Except ε (Option PUnit × σ)
          let o := mkApp (mkConst ``Option [mi.u]) (← mkPUnit)
          let oσ := mkApp2 (mkConst ``Prod [mi.u, mi.u]) o σ
          let eoσ := mkApp2 (mkConst ``Except [mi.u, mi.u]) ε oσ
          let mutVars := (← read).mutVars

          -- Introduce proxy FVs for *all* mut vars. `elimProxyDefs` will later on replace them with
          -- actual reassigned or original definitions.
          -- Side note: SG tried to do this without introducing proxy FVs, instead setting the
          -- `nondep` flag for all mut var defs here and then replacing those that were reassigned
          -- with their actual definitions in terms of `loopS`.
          -- However, that led to strange unification errors and SG abandoned the idea.
          withProxyMutVarDefs fun elimProxyDefs => do

          -- We need to delay filling in continueK and breakK because they take a `σ` tuple
          let loopBodyCtx ← getLCtx
          let continueK ← mkFreshContVar eoσ
          let breakK ← mkFreshContVar eoσ
          let returnK (e : Expr) : DoElabM Expr := do
            -- We can fill in `returnK` now because it does not depend on `σ`
            let e ← Term.ensureHasType ε e
            return mkApp5 (mkConst ``EarlyReturnT.return [mi.u, mi.v]) ε oσ mi.m instMonad e

          -- Elaborate the loop body.
          let block ← enterLoopBody eoσ returnK breakK.mkJump continueK.mkJump do
            let n ← mkFreshUserName `r
            elabElems1 (getDooElems dooSeq) (DoElemCont.cont n (← mkPUnit) continueK.mkJump)

          -- Compute the set of reassigned mut vars and its complement.
          -- Take care to preserve the declaration order that is manifest in the array `mutVars`.
          let reassignedMutVars ← do
            let cont ← continueK.getReassignedMutVars loopBodyCtx
            let brk ← breakK.getReassignedMutVars loopBodyCtx
            pure (mutVars.filter (cont ++ brk).contains)

          -- Assign the state tuple type and the initial tuple of states.
          preS.mvarId!.withContext do
            let defs ← reassignedMutVars.mapM (getFVarFromUserName ·)
            let (tuple, tupleTy) ← mkProdMkN defs
            discard <| isDefEq preS tuple
            discard <| isDefEq σ tupleTy

          -- Synthesize the `break` and `continue` jumps.
          continueK.synthesizeJumps do
            let (tuple, _tupleTy) ← mkProdMkN (← reassignedMutVars.mapM (getFVarFromUserName ·))
            let tuple ← Term.ensureHasType σ tuple
            return mkApp5 (mkConst ``BreakT.continue [mi.u, mi.v]) σ ε mi.m instMonad tuple
          breakK.synthesizeJumps do
            let (tuple, _tupleTy) ← mkProdMkN (← reassignedMutVars.mapM (getFVarFromUserName ·))
            let tuple ← Term.ensureHasType σ tuple
            return mkApp5 (mkConst ``BreakT.break [mi.u, mi.v]) σ ε mi.m instMonad tuple

          let block ← bindMutVarsFromTuple reassignedMutVars.toList loopS.fvarId! do
            -- Replace the proxy variables with their actual definitions, as if we never introduced
            -- them in the first place.
            elimProxyDefs block
          let body ← mkLambdaFVars #[x, loopS] block

          return (body, reassignedMutVars)

      let kreturn ← withLocalDeclD (← mkFreshUserName `r) ε fun r => do mkLambdaFVars #[r] <| ← do
        let k ← getReturnCont
        k r
      let kafter ← withLocalDeclD (← mkFreshUserName `s) σ fun postS => do mkLambdaFVars #[postS] <| ← do
        bindMutVarsFromTuple reassignedMutVars.toList postS.fvarId! do
          let k ← k.continueWithUnit dooElem
          Term.ensureHasType (← mkMonadicType γ) k
      let instFoldable ← Term.mkInstMVar <| mkApp2 (mkConst ``Foldable [uρ, uα, mi.u]) ρ α
      let app := mkConst ``Foldable.forBreak_ [uρ, uα, mi.u, mi.v]
      let app := mkApp5 app ρ α instFoldable mi.m instMonad
      let app := mkApp8 app σ ε γ xs preS body kreturn kafter
      return app
    | _ => throwErrorAt dooElem "unexpected do element {dooElem}"

  meta def elabElems1 (dooElems : Array (TSyntax `dooElem)) (k : DoElemCont) : DoElabM Expr := do
    let last := dooElems.back!
    let init := dooElems.pop
    let unit ← mkPUnit
    let r ← mkFreshUserName `r
    init.foldr (init := elabElem last k) fun el k => elabElem el (.cont r unit k)

end

meta def elabDooBlock (dooSeq : TSyntax `dooSeq) (expectedType? : Expr) : TermElabM Expr := do
  -- trace[Elab.do] "Doo block: {dooSeq}, expectedType?: {expectedType?}"
  Term.tryPostponeIfNoneOrMVar expectedType?
  let ctx ← mkContext expectedType?
  let res ← elabElems1 (getDooElems dooSeq) (.last ctx.doBlockResultType) |>.run ctx |>.run' {}
  -- logInfo m!"res: {res}"
  pure res

elab_rules : term <= expectedType?
  | `(dooBlock| doo $dooSeq) => elabDooBlock dooSeq expectedType?

set_option trace.Elab.do true in
set_option pp.raw false in
#check Id.run (α := Nat) doo
  let mut x ← pure 42
  let y ←
    if true then
      pure ()
    else
      pure ()
  x := x + 3
  return x
set_option pp.mvars.delayed false in
set_option trace.Meta.synthInstance true in
set_option trace.Elab.step false in
set_option trace.Elab.do true in
set_option trace.Elab.postpone true in
set_option pp.raw false in
#check doo return 42
#check doo pure (); return 42
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
#check doo let mut x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check doo let x : Nat := 0; if true then {pure ()} else {pure ()}; pure 13
#check Id.run doo
  let mut x ← pure 42
  let mut z := 0
  z ←
    if true then
      return z
    else
      pure 4
  x := x + 3
  return x

/--
info: (let x := 42;
  let y := 0;
  let z := 1;
  Foldable.forBreak_ [1, 2, 3] (x, z)
    (fun i s =>
      let x := s.fst;
      let z := s.snd;
      let x_1 := x + i;
      let __do_jp := fun z r =>
        let z_1 := z + i;
        BreakT.continue (x + i, z + i);
      if x_1 > 10 then
        let z := z + i;
        __do_jp z PUnit.unit
      else __do_jp z PUnit.unit)
    (fun r => pure r) fun s =>
    let x := s.fst;
    let z := s.snd;
    pure (x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    if x > 10 then z := z + i
    z := z + i
  return x + y + z)

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.isDefEq.delta true in
-- set_option trace.Meta.isDefEq.assign true in
-- set_option trace.Elab.do true in
/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  Foldable.forBreak_ [1, 2, 3] (x, y, z)
    (fun i s =>
      let x := s.fst;
      let s := s.snd;
      let y := s.fst;
      let z := s.snd;
      let __do_jp := fun z r =>
        if x > 10 then
          let x_1 := x + 3;
          BreakT.continue (x + 3, y, z)
        else
          if x < 20 then
            let y_1 := y - 2;
            BreakT.break (x, y - 2, z)
          else BreakT.continue (x + i, y, z);
      if x = 3 then
        let z := z + i;
        __do_jp z PUnit.unit
      else __do_jp z PUnit.unit)
    (fun r => pure r) fun s =>
    let x := s.fst;
    let s := s.snd;
    let y := s.fst;
    let z := s.snd;
    pure (w + x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    if x < 20 then y := y - 2; break
    x := x + i
  return w + x + y + z

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 68
    def List.foldrNonTR._at_.Do._example.spec_0 w _x.1 _x.2 x.3 _y.4 : Nat :=
      fun _f.5 s.6 : Nat :=
        let x := s.6 # 0;
        let s.7 := s.6 # 1;
        let y := s.7 # 0;
        let z := s.7 # 1;
        let _x.8 := Nat.add w x;
        let _x.9 := Nat.add _x.8 y;
        let _x.10 := Nat.add _x.9 z;
        return _x.10;
      fun _f.11 a acc s : Nat :=
        jp _jp.12 _y.13 : Nat :=
          cases _y.13 : Nat
          | Except.error a.14 =>
            return a.14
          | Except.ok a.15 =>
            cases a.15 : Nat
            | Prod.mk fst.16 snd.17 =>
              cases fst.16 : Nat
              | Option.none =>
                let _x.18 := _f.5 snd.17;
                return _x.18
              | Option.some val.19 =>
                let _x.20 := acc snd.17;
                return _x.20;
        let x := s # 0;
        let s.21 := s # 1;
        let y := s.21 # 0;
        fun _f.22 z r.23 : Except Nat (Option PUnit × Nat × Nat × Nat) :=
          let _x.24 := 10;
          let _x.25 := Nat.decLt _x.24 x;
          cases _x.25 : Except Nat (Option PUnit × Nat × Nat × Nat)
          | Decidable.isFalse x.26 =>
            let _x.27 := 20;
            let _x.28 := Nat.decLt x _x.27;
            cases _x.28 : Except Nat (Option PUnit × Nat × Nat × Nat)
            | Decidable.isFalse x.29 =>
              let _x.30 := Nat.add x a;
              let _x.31 := @Prod.mk _ _ y z;
              let _x.32 := @Prod.mk _ _ _x.30 _x.31;
              let _x.33 := PUnit.unit;
              let _x.34 := @some _ _x.33;
              let _x.35 := @Prod.mk _ _ _x.34 _x.32;
              let _x.36 := @Except.ok _ _ _x.35;
              return _x.36
            | Decidable.isTrue x.37 =>
              let y := Nat.sub y _x.1;
              let _x.38 := @Prod.mk _ _ y z;
              let _x.39 := @Prod.mk _ _ x _x.38;
              let _x.40 := @none _;
              let _x.41 := @Prod.mk _ _ _x.40 _x.39;
              let _x.42 := @Except.ok _ _ _x.41;
              return _x.42
          | Decidable.isTrue x.43 =>
            let x := Nat.add x _x.2;
            let _x.44 := @Prod.mk _ _ y z;
            let _x.45 := @Prod.mk _ _ x _x.44;
            let _x.46 := PUnit.unit;
            let _x.47 := @some _ _x.46;
            let _x.48 := @Prod.mk _ _ _x.47 _x.45;
            let _x.49 := @Except.ok _ _ _x.48;
            return _x.49;
        let z := s.21 # 1;
        let _x.50 := instDecidableEqNat x _x.2;
        cases _x.50 : Nat
        | Decidable.isFalse x.51 =>
          let _x.52 := PUnit.unit;
          let _x.53 := _f.22 z _x.52;
          goto _jp.12 _x.53
        | Decidable.isTrue x.54 =>
          let z := Nat.add z a;
          let _x.55 := PUnit.unit;
          let _x.56 := _f.22 z _x.55;
          goto _jp.12 _x.56;
      cases x.3 : Nat
      | List.nil =>
        let _x.57 := _f.5 _y.4;
        return _x.57
      | List.cons head.58 tail.59 =>
        let _x.60 := @List.foldrNonTR _ _ _f.11 _f.5 tail.59;
        let _x.61 := _f.11 head.58 _x.60 _y.4;
        return _x.61
[Compiler.saveBase] size: 13
    def Do._example : Nat :=
      let w := 23;
      let x := 42;
      let y := 0;
      let z := 1;
      let _x.1 := 2;
      let _x.2 := 3;
      let _x.3 := @List.nil _;
      let _x.4 := @List.cons _ _x.2 _x.3;
      let _x.5 := @List.cons _ _x.1 _x.4;
      let _x.6 := @List.cons _ z _x.5;
      let _x.7 := @Prod.mk _ _ y z;
      let _x.8 := @Prod.mk _ _ x _x.7;
      let _x.9 := List.foldrNonTR._at_.Do._example.spec_0 w _x.1 _x.2 _x.6 _x.8;
      return _x.9
-/
#guard_msgs in
example := Id.run doo
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    if x < 20 then y := y - 2; break
    x := x + i
  return w + x + y + z

/--
info: (let w := 23;
  let x := 42;
  let y := 0;
  let z := 1;
  do
  let r ←
    forIn [1, 2, 3] ⟨x, y, z⟩ fun i r =>
        let x := r.fst;
        let x_1 := r.snd;
        let y := x_1.fst;
        let z := x_1.snd;
        let __do_jp := fun x y z y_1 =>
          let __do_jp := fun x y y_2 =>
            let __do_jp := fun x y y_3 =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨x, y, z⟩);
            if x < 20 then
              let y := y - 2;
              pure (ForInStep.done ⟨x, y, z⟩)
            else do
              let y_3 ← pure PUnit.unit
              __do_jp x y y_3;
          if x > 10 then
            let x := x + 3;
            pure (ForInStep.yield ⟨x, y, z⟩)
          else do
            let y_2 ← pure PUnit.unit
            __do_jp x y y_2;
        if x = 3 then
          let z := z + i;
          do
          let y_1 ← pure PUnit.unit
          __do_jp x y z y_1
        else do
          let y_1 ← pure PUnit.unit
          __do_jp x y z y_1
  match r with
    | ⟨x, y, z⟩ => pure (w + x + y + z)).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut w := 23
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    if x = 3 then z := z + i
    if x > 10 then x := x + 3; continue
    if x < 20 then y := y - 2; break
    x := x + i
  return w + x + y + z)

set_option trace.Compiler.saveBase true in
/--
trace: [Compiler.saveBase] size: 29
    def List.foldrNonTR._at_.Do._example.spec_0 _x.1 _x.2 x.3 _y.4 : Nat :=
      fun _f.5 s.6 : Nat :=
        let _x.7 := 13;
        let x := Nat.add s.6 _x.7;
        let x := Nat.add x _x.7;
        let x := Nat.add x _x.7;
        let x := Nat.add x _x.7;
        return x;
      cases x.3 : Nat
      | List.nil =>
        let _x.8 := _f.5 _y.4;
        return _x.8
      | List.cons head.9 tail.10 =>
        let _x.11 := instDecidableEqNat _y.4 _x.1;
        cases _x.11 : Nat
        | Decidable.isFalse x.12 =>
          let _x.13 := 10;
          let _x.14 := Nat.decLt _x.13 _y.4;
          cases _x.14 : Nat
          | Decidable.isFalse x.15 =>
            let _x.16 := 20;
            let _x.17 := Nat.decLt _y.4 _x.16;
            cases _x.17 : Nat
            | Decidable.isFalse x.18 =>
              let _x.19 := Nat.add _y.4 head.9;
              let _x.20 := List.foldrNonTR._at_.Do._example.spec_0 _x.1 _x.2 tail.10 _x.19;
              return _x.20
            | Decidable.isTrue x.21 =>
              let x := Nat.mul _y.4 _x.2;
              let _x.22 := _f.5 x;
              return _x.22
          | Decidable.isTrue x.23 =>
            let x := Nat.add _y.4 _x.1;
            let _x.24 := List.foldrNonTR._at_.Do._example.spec_0 _x.1 _x.2 tail.10 x;
            return _x.24
        | Decidable.isTrue x.25 =>
          return _y.4
[Compiler.saveBase] size: 9
    def Do._example : Nat :=
      let x := 42;
      let _x.1 := 1;
      let _x.2 := 2;
      let _x.3 := 3;
      let _x.4 := @List.nil _;
      let _x.5 := @List.cons _ _x.3 _x.4;
      let _x.6 := @List.cons _ _x.2 _x.5;
      let _x.7 := @List.cons _ _x.1 _x.6;
      let _x.8 := List.foldrNonTR._at_.Do._example.spec_0 _x.3 _x.2 _x.7 x;
      return _x.8
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  for i in [1,2,3] doo
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x

set_option trace.Compiler.specialize.candidate true in
/--
trace: [Compiler.specialize.candidate] List.foldrNonTR _f.582 _f.102 _x.21 _x.22, [N, N, U, U, O]
[Compiler.specialize.candidate] key: fun _x.15 x z =>
      List.foldrNonTR
        (fun a acc s =>
          have x_1 := s.1;
          have z_1 := s.2;
          have x_2 := x_1.add a;
          have _f.713 := fun s.714 =>
            have _x.715 := (x_2, s.714);
            have _x.716 := PUnit.unit;
            have _x.717 := some _x.716;
            have _x.718 := (_x.717, _x.715);
            have _x.719 := Except.ok _x.718;
            _x.719;
          have _f.720 := fun a_1 acc s =>
            have _jp.766 := fun _y.765 =>
              cases _y.765
                (Except.error fun a.722 =>
                  have _x.723 := Except.error a.722;
                  _x.723)
                (Except.ok fun a.724 =>
                  cases a.724
                    (Prod.mk fun fst.725 snd.726 =>
                      cases fst.725
                        (none
                          (have _x.727 := _f.713 snd.726;
                          _x.727))
                        (some fun val.728 =>
                          have _x.729 := acc snd.726;
                          _x.729)));
            have _f.731 := fun z r.732 =>
              have _x.733 := 8;
              have _x.734 := _x.733.decLt a_1;
              cases _x.734 isFalse isTrue;
            have _x.757 := 5;
            have _x.758 := a_1.decLt _x.757;
            cases _x.758 isFalse isTrue;
          have _x.667 := 10;
          have _x.668 := _x.667.sub a;
          have _x.669 := _x.668.add z;
          have _x.670 := 1;
          have _x.671 := _x.669.sub _x.670;
          have _x.673 := z.mul _x.671;
          have _x.674 := a.add _x.673;
          have _x.675 := [];
          have _x.676 := List.range'TR.go z _x.671 _x.674 _x.675;
          have _x.730 := List.foldrNonTR _f.720 _f.713 _x.676 z_1;
          cases _x.730 (Except.error fun a.660 => a.660)
            (Except.ok fun a.661 =>
              cases a.661
                (Prod.mk fun fst.662 snd.663 =>
                  cases fst.662
                    (none
                      (have _x.664 :=
                        (fun s.90 =>
                            have x := s.90.1;
                            have z := s.90.2;
                            have _x.577 := x.add z;
                            _x.577)
                          snd.663;
                      _x.664))
                    (some fun val.665 =>
                      have _x.666 := acc snd.663;
                      _x.666))))
        fun s.90 =>
        have x := s.90.1;
        have z := s.90.2;
        have _x.577 := x.add z;
        _x.577
[Compiler.specialize.candidate] List.foldrNonTR _f.776 _f.773 tail.848, [N, N, U, U, O]
[Compiler.specialize.candidate] key: fun _x.772 x z =>
      List.foldrNonTR
        (fun a acc s =>
          have x_1 := s.1;
          have z_1 := s.2;
          have x_2 := x_1.add a;
          have _f.777 := fun s.778 =>
            have _x.779 := (x_2, s.778);
            have _x.780 := PUnit.unit;
            have _x.781 := some _x.780;
            have _x.782 := (_x.781, _x.779);
            have _x.783 := Except.ok _x.782;
            _x.783;
          have _f.784 := fun a_1 acc s =>
            have _jp.785 := fun _y.786 =>
              cases _y.786
                (Except.error fun a.787 =>
                  have _x.788 := Except.error a.787;
                  _x.788)
                (Except.ok fun a.789 =>
                  cases a.789
                    (Prod.mk fun fst.790 snd.791 =>
                      cases fst.790
                        (none
                          (have _x.792 := _f.777 snd.791;
                          _x.792))
                        (some fun val.793 =>
                          have _x.794 := acc snd.791;
                          _x.794)));
            have _f.795 := fun z r.796 =>
              have _x.797 := 8;
              have _x.798 := _x.797.decLt a_1;
              cases _x.798 isFalse isTrue;
            have _x.821 := 5;
            have _x.822 := a_1.decLt _x.821;
            cases _x.822 isFalse isTrue;
          have _x.829 := 10;
          have _x.830 := _x.829.sub a;
          have _x.831 := _x.830.add z;
          have _x.832 := 1;
          have _x.833 := _x.831.sub _x.832;
          have _x.834 := z.mul _x.833;
          have _x.835 := a.add _x.834;
          have _x.836 := [];
          have _x.837 := List.range'TR.go z _x.833 _x.835 _x.836;
          have _x.838 := List.foldrNonTR _f.784 _f.777 _x.837 z_1;
          cases _x.838 (Except.error fun a.839 => a.839)
            (Except.ok fun a.840 =>
              cases a.840
                (Prod.mk fun fst.841 snd.842 =>
                  cases fst.841
                    (none
                      (have _x.843 :=
                        (fun s.774 =>
                            have x := s.774.1;
                            have z := s.774.2;
                            have _x.775 := x.add z;
                            _x.775)
                          snd.842;
                      _x.843))
                    (some fun val.844 =>
                      have _x.845 := acc snd.842;
                      _x.845))))
        fun s.774 =>
        have x := s.774.1;
        have z := s.774.2;
        have _x.775 := x.add z;
        _x.775
-/
#guard_msgs in
example := Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    for j in [i:10].toList doo
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z

/--
info: (let x := 42;
  do
  let r ←
    forIn [1, 2, 3] ⟨none, x⟩ fun i r =>
        let r_1 := r.snd;
        let x := r_1;
        let __do_jp := fun x y =>
          let __do_jp := fun x y =>
            let __do_jp := fun x y =>
              let x := x + i;
              do
              pure PUnit.unit
              pure (ForInStep.yield ⟨none, x⟩);
            if x < 20 then
              let x := x * 2;
              pure (ForInStep.done ⟨none, x⟩)
            else do
              let y ← pure PUnit.unit
              __do_jp x y;
          if x > 10 then
            let x := x + 3;
            pure (ForInStep.yield ⟨none, x⟩)
          else do
            let y ← pure PUnit.unit
            __do_jp x y;
        if x = 3 then pure (ForInStep.done ⟨some x, x⟩)
        else do
          let y ← pure PUnit.unit
          __do_jp x y
  let x : Nat := r.snd
  let __do_jp : Nat → PUnit → Id Nat := fun x y =>
    let x := x + 13;
    let x := x + 13;
    let x := x + 13;
    let x := x + 13;
    pure x
  match r.fst with
    | none => do
      let y ← pure PUnit.unit
      __do_jp x y
    | some a => pure a).run : Nat
-/
#guard_msgs (info) in
#check (Id.run do
  let mut x := 42
  for i in [1,2,3] do
    if x = 3 then return x
    if x > 10 then x := x + 3; continue
    if x < 20 then x := x * 2; break
    x := x + i
  x := x + 13
  x := x + 13
  x := x + 13
  x := x + 13
  return x)

example : (Id.run doo pure 42)
        = (Id.run  do pure 42) := by rfl
example : (Id.run doo return 42)
        = (Id.run  do return 42) := by rfl
example {e : Id PUnit} : (Id.run doo e)
                       = (Id.run  do e) := by rfl
example {e : Id PUnit} : (Id.run doo e; return 42)
                       = (Id.run  do e; return 42) := by rfl
example : (Id.run doo let x := 42; return x + 13)
        = (Id.run  do let x := 42; return x + 13) := by rfl
example : (Id.run doo let x ← pure 42; return x + 13)
        = (Id.run  do let x ← pure 42; return x + 13) := by rfl
example : (Id.run doo let mut x := 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x := 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; x := x + 1; return x + 13)
        = (Id.run  do let mut x ← pure 42; x := x + 1; return x + 13) := by rfl
example : (Id.run doo let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; if true then {x := x + 1; return x} else {x := x + 3}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x)
        = (Id.run  do let mut x ← pure 42; let mut _x ← if true then {x := x + 1; let y ← pure 3; return y}; x := x + 13; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x)
        = (Id.run  do let mut x ← pure 42; x ← if true then {x := x + 1; return x} else {x := x + 2; pure 4}; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; let mut _x ← if true then {z := z + 1; let y ← pure 3; return y} else {z := z + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x)
        = (Id.run  do let mut x ← pure 42; let mut z := 0; z ← if true then {x := x + 1; return z} else {x := x + 2; pure 4}; x := x + z; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : (Id.run doo let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x)
        = (Id.run  do let mut x ← pure 42; let y ← if true then {pure 3} else {pure 4}; x := x + y; return x) := by rfl
example : Nat := Id.run doo let mut foo : Nat = Nat := rfl; pure (foo ▸ 23)

-- Test: Nested if-then-else with multiple mutable variables
example : (Id.run doo
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y)
= (Id.run do
  let mut x := 0
  let mut y := 1
  if true then
    if false then
      x := 10
      y := 20
    else
      x := 5
      y := 15
  else
    x := 100
  return x + y) := by rfl

-- Test: Multiple reassignments in sequence
example : (Id.run doo
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x)
= (Id.run do
  let mut x := 10
  x := x + 1
  x := x * 2
  x := x - 3
  return x) := by rfl

-- Test: Monadic bind with complex RHS
example : (Id.run doo
  let x ← (do let y := 5; pure (y + 3))
  return x * 2)
= (Id.run do
  let x ← (do let y := 5; pure (y + 3))
  return x * 2) := by rfl
#print Eq.casesOn

-- Test: Mutable variable reassignment through monadic bind
set_option trace.Meta.isDefEq true in
example : (Id.run doo
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x)
= (Id.run do
  let mut x := 1
  x ← pure (x + 10)
  x ← pure (x * 2)
  return x) := by rfl

-- Test: Multiple mutable variables with different reassignment patterns
example : (Id.run doo
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c))
= (Id.run do
  let mut a := 1
  let mut b := 2
  let mut c := 3
  if true then
    a := a + 1
  else
    b := b + 1
  c := a + b
  return (a, b, c)) := by rfl

-- Test: Let binding followed by mutable reassignment
example : (Id.run doo
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y))
= (Id.run do
  let x := 5
  let mut y := x
  y := y * 2
  return (x, y)) := by rfl

-- Test: Early return in else branch
example : (Id.run doo
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x)
= (Id.run do
  let mut x := 0
  if false then
    x := 10
  else
    return 42
  x := 20
  return x) := by rfl

-- Test: Both branches return
example : (Id.run doo
  let mut x := 0
  if true then
    return 1
  else
    return 2)
= (Id.run do
  let mut x := 0
  if true then
    return 1
  else
    return 2) := by rfl

-- Test: Three-level nested if with mutable variables
example : (Id.run doo
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x)
= (Id.run do
  let mut x := 0
  if true then
    if true then
      if false then
        x := 1
      else
        x := 2
    else
      x := 3
  else
    x := 4
  return x) := by rfl

-- Test: Mutable variable used in condition
example : (Id.run doo
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x)
= (Id.run do
  let mut x := 5
  if x > 3 then
    x := x * 2
  else
    x := x + 1
  return x) := by rfl

-- Test: Multiple monadic binds in sequence
example : (Id.run doo
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c))
= (Id.run do
  let a ← pure 1
  let b ← pure (a + 1)
  let c ← pure (a + b)
  return (a + b + c)) := by rfl

-- Test: Mutable bind in if condition position
example : (Id.run doo
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x)
= (Id.run do
  let mut x := 0
  let y ← if x == 0 then pure 1 else pure 2
  x := y
  return x) := by rfl

-- Test: Empty else branch behavior
example : (Id.run doo
  let mut x := 5
  if false then
    x := 10
  return x)
= (Id.run do
  let mut x := 5
  if false then
    x := 10
  return x) := by rfl

-- Test: Nested doo with if and early return
example : (Id.run doo
  let mut x := 10
  let y ← doo
    if true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y)
= (Id.run do
  let mut x := 10
  let y ← do
    if true then
      x := x + 3
      pure 42
    else
      return 13
  return x + y) := by rfl

-- For loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  for i in [0:100].toList doo
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x)
= (Id.run do
  let mut x := 42
  for i in [0:100].toList do
    if i = 40 then return x
    if i > 20 then x := x + 3; break
    if i < 20 then x := x * 2; continue
    x := x + i
  x := x + 13
  x := x + 13
  return x) := by rfl

-- Nested for loops with break, continue and return
example :
  (Id.run doo
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] doo
    x := x + i
    for j in [i:10].toList doo
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z)
= (Id.run do
  let mut x := 42
  let mut y := 0
  let mut z := 1
  for i in [1,2,3] do
    x := x + i
    for j in [i:10].toList do
      if j < 5 then z := z + j
      if j > 8 then return 42
      if j < 3 then continue
      if j > 6 then break
      z := z + i
  return x + y + z) := by rfl

/-!
Postponing Monad instance resolution appropriately
-/

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.8
-/
#guard_msgs (error) in
example := doo return 42
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Bind ?m.11
-/
#guard_msgs (error) in
example := doo let x <- ?z; ?y
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.12
-/
#guard_msgs (error) in
example := do return 42
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Bind ?m.16
-/
#guard_msgs (error) in
example := do let x <- ?z; ?y

-- This tests that inferred types are correctly propagated outwards.
example {e : Id Nat} := doo if true then e else pure 13
-- We do want to be able to `#check` the following example (including the last `pure`) without an
-- expected monad, ...
#check doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x
-- As well as fully resolve all instances in the following example where the expected monad is
-- known. The next example wouldn't work without `Id.run`.
example := Id.run doo let mut x : Nat := 0; if true then {x := x + 1} else {pure ()}; pure x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 42; x := x - 7; let x := x + 4; return x + 13)

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
-/
#guard_msgs (error) in
example := (Id.run doo pure true; pure ())

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure true
---
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure true} else {pure false}; pure ())

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  PUnit
in the application
  pure false
-/
#guard_msgs (error) in
example := (Id.run doo if true then {pure ()} else {pure false}; pure ())

-- Additional error tests

/-- error: unknown local declaration `foo` -/
#guard_msgs (error) in
example := (Id.run doo foo := 42; pure ())

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs (error) in
example := (Id.run doo let mut x := 1; if true then {let mut x := 2; pure ()} else {pure ()}; pure x)

-- Regression test cases of what's currently broken in the do elaborator:
example : Unit := (Id.run do  let n ← if true then pure 3 else pure 42)
example : Unit := (Id.run doo let n ← if true then pure 3 else pure 42)
example := (Id.run do  let mut x := 0; x ← return 10)
example := (Id.run doo let mut x := 0; x ← return 10)

/--
info: let x := 0;
let y := 0;
if true = true then pure 3
else
  let x := x + 5;
  let y_1 := 3;
  pure (x + y) : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    return 3
  else
    x := x + 5
    let y := 3
  return x + y

/--
info: let x := 0;
let y := 0;
let __do_jp := fun x r => pure (x + y);
if true = true then
  let x := x + 7;
  let y := 3;
  __do_jp x PUnit.unit
else
  let x := x + 5;
  __do_jp x PUnit.unit : ?m Nat
-/
#guard_msgs (info) in
#check doo
  let mut x : Nat := 0
  let y := 0
  if true then
    x := x + 7
    let y := 3
  else
    x := x + 5
  return x + y

open Std.Do
class WPAttach (m : Type u → Type v) (ps : outParam (PostShape.{u})) [Monad m] extends WP m ps where
  attach (prog : m α) (p : α → Prop) (h : ⦃⌜True⌝⦄ prog ⦃⇓r => ⌜p r⌝⦄) : ∃ (prog' : m (Subtype p)), prog = Subtype.val <$> prog'

instance : WPAttach Id .pure where
  attach prog _ h := ⟨⟨prog, h .intro⟩, rfl⟩

instance [Monad m] [LawfulMonad m] [WPAttach m ps] : WPAttach (StateT σ m) (.arg σ ps) where
  attach prog p h := by
    let f (s : σ) := WPAttach.attach (prog s) (fun (a, s') => p a) (h s)
    exists fun s => (fun ⟨⟨a, s'⟩, h⟩ => ⟨⟨a, h⟩, s'⟩) <$> (f s).choose
    ext s
    simp [Functor.map, StateT.map, StateT.run]
    conv => lhs; rw [(f s).choose_spec]

instance [Monad m] [WPAttach m ps] : WPAttach (ReaderT ρ m) (.arg ρ ps) where
  attach prog p h := by
    let f (r : ρ) := WPAttach.attach (prog r) p (h r)
    exists fun r => (f r).choose
    ext r
    simp [Functor.map, ReaderT.run]
    conv => lhs; rw [(f r).choose_spec]

instance [Monad m] [LawfulMonad m] [WPAttach m ps] : WPAttach (ExceptT ε m) (.except ε ps) where
  attach prog p h := by
    have h'  : ∃ prog', prog.run = Subtype.val <$> prog' := WPAttach.attach (ps:=ps) prog.run (fun | .ok a => p a | _ => False) <| by
      simp [Triple, WP.wp] at h
      simp [Triple, ExceptT.run]
      apply SPred.entails.trans h
      apply SPred.bientails.mp
      apply SPred.bientails.of_eq
      congr; ext x; split <;> rfl
    exists ExceptT.mk <| (fun | ⟨.ok a, h⟩ => Except.ok ⟨a, h⟩ | ⟨.error e, _⟩ => Except.error e) <$> h'.choose
    ext
    conv => lhs; rw [h'.choose_spec]
    simp [ExceptT.mk, ExceptT.run, Functor.map, ExceptT.map]
    rw [map_eq_pure_bind]
    congr
    ext x
    match x with
    | .mk a h =>
    cases a <;> rfl

instance [Monad m] [LawfulMonad m] [WPAttach m ps] : WPAttach (OptionT m) (.except PUnit ps) where
  attach prog p h := by
    have h'  : ∃ prog', prog.run = Subtype.val <$> prog' := WPAttach.attach (ps:=ps) prog.run (fun | .some a => p a | _ => False) <| by
      simp [Triple, WP.wp] at h
      simp [Triple]
      apply SPred.entails.trans h
      apply SPred.bientails.mp
      apply SPred.bientails.of_eq
      congr; ext x; split <;> rfl
    exists OptionT.mk <| (fun | ⟨.some a, h⟩ => Option.some ⟨a, h⟩ | ⟨.none, _⟩ => Option.none) <$> h'.choose
    ext
    conv => lhs; rw [h'.choose_spec]
    simp [OptionT.mk, OptionT.run, Functor.map, OptionT.bind, OptionT.pure]
    rw [map_eq_pure_bind]
    congr
    ext x
    match x with
    | .mk a h =>
    cases a <;> rfl

class Foldable (ρ : Type u) (α : outParam (Type v)) where
  foldr : (α → β → β) → β → ρ → β

instance : Foldable (List α) α where
  foldr := List.foldr

class ForBreak (m : Type u → Type v) (ρ : Sort w) (α : outParam (Type v)) where
  forBreak_ (f : α → OptionT m PUnit) (xs : ρ) : m PUnit

instance [Foldable ρ α] [Monad m] : ForBreak m ρ α where
  forBreak_ f xs :=
    Foldable.foldr (fun x acc _ => SeqRight.seqRight (f x) (liftM ∘ acc) |>.run |> discard) pure xs ()


/--
A proof that the given loop body `prog` either breaks (i.e., returns `none`) or decreases according
to the well-founded relation `rel` when run on the initial state `s`.
-/
def DecreasesOn {σ m α} (rel : α → σ → σ → Prop) [Monad m] (prog : OptionT (StateT σ m) α) (s : σ) :=
  ∃ prog' : m { p // p.1.casesOn True (fun a => rel a p.2 s) },
    prog s = Subtype.val <$> prog'

/--
A proof that the `body` of a while loop terminates according to the well-founded relation `rel`.
-/
structure LoopUntilBreak (rel : σ → σ → Prop) [Monad m]
    (body : PUnit → OptionT (StateT σ m) PUnit) : Prop where
  wf : WellFounded rel
  bodyDecreases : ∀ s, DecreasesOn (fun _ => rel) (body ⟨⟩) s

-- The usual `partial def`-implementation-for-`WellFounded.fix`-definition dance


namespace Std.Internal

variable {α : Sort _} {β : α → Sort _} {C : α → Sort _} {C₂ : (a : α) → β a → Sort _}

@[specialize]
public partial def opaqueFix [∀ x, Nonempty (C x)] (F : (x : α) → ((y : α) → C y) → C x) (x : α) : C x :=
  F x (opaqueFix F)

@[expose]
public def TerminatesTotally (F : (x : α) → ((y : α) → C y) → C x) : Prop :=
  ∃ (r : α → α → Prop) (F' : (x : α) → ((y : α) → r y x → C y) → C x), WellFounded r ∧ ∀ x G, F x G = F' x (fun x _ => G x)

/-
SAFE assuming that the code generated by iteration over `F` is compatible
with the kernel semantics of iteration over `F' : (x : α) → ((y : α) → r y x → C y) → C x`
for all `F'` as in `TerminatesTotally`.
-/
@[implemented_by opaqueFix]
public def extrinsicFix [∀ x, Nonempty (C x)] (F : (x : α) → ((y : α) → C y) → C x) (x : α) : C x :=
  open scoped Classical in
  if h : TerminatesTotally F then
    let F' := h.choose_spec.choose
    let h := h.choose_spec.choose_spec
    h.1.fix F' x
  else
    opaqueFix F x

public def extrinsicFix_eq [∀ x, Nonempty (C x)] {F : (x : α) → ((y : α) → C y) → C x}
    (h : TerminatesTotally F) {x : α} :
    extrinsicFix F x = F x (extrinsicFix F) := by
  simp only [extrinsicFix, dif_pos h]
  rw [WellFounded.fix_eq, show (extrinsicFix F) = (fun y => extrinsicFix F y) by rfl]
  simp only [extrinsicFix, dif_pos h, h.choose_spec.choose_spec.2]

end Std.Internal

/--
Iterate a loop body `body : PUnit → OptionT (StateT σ m) PUnit` until it breaks (i.e., returns `none`).
Every iteration must decrease in the state `σ` according to the well-founded relation `rel`.

It is `loopUntilBreak body dw = discard (do body ⟨⟩; liftM (loopUntilBreak body dw)).run`.
-/
def extrinsicLoopUntilBreak {σ : Type u} {m : Type u → Type v} [Monad m]
    (body : PUnit.{max u v + 1} → OptionT (StateT σ m) PUnit)
    : StateT σ m PUnit :=
  @Std.Internal.extrinsicFix _ _ (fun s => ⟨pure (PUnit.unit, s)⟩) F
where
  F (s : σ) (recur : (s' : σ) → m (PUnit × σ)) : m (PUnit × σ) := do
    let (u?, s') ← (body ⟨⟩).run s
    match u? with
    | none => pure (⟨⟩, s')
    | some _ => recur s'

/--
Iterate a loop body `body : PUnit → OptionT (StateT σ m) PUnit` until it breaks (i.e., returns `none`).
Every iteration must decrease in the state `σ` according to the well-founded relation `rel`.

It is `loopUntilBreak body dw = discard (do body ⟨⟩; liftM (loopUntilBreak body dw)).run`.
-/
def intrinsicLoopUntilBreak {σ : Type u} {m : Type u → Type v} {rel : σ → σ → Prop} [Monad m]
    (body : PUnit.{max u v + 1} → OptionT (StateT σ m) PUnit)
    (dw : LoopUntilBreak rel body) : StateT σ m PUnit :=
  extrinsicLoopUntilBreak body

theorem Std.Internal.TerminatesTotally.ofLoopUntilBreak {σ : Type u} {m : Type u → Type v} {rel : σ → σ → Prop}
    [Monad m] [LawfulMonad m]
    (body : PUnit.{max u v + 1} → OptionT (StateT σ m) PUnit)
    (dw : LoopUntilBreak rel body) : TerminatesTotally (extrinsicLoopUntilBreak.F body) := by
  exists rel
  exists fun s recur => do
    let ⟨⟨u?, s'⟩, h⟩ ← (dw.bodyDecreases s).choose
    match _ : u? with
    | none => pure (⟨⟩, s')
    | some _ => recur s' h
  constructor
  · exact dw.wf
  · intro s _
    unfold extrinsicLoopUntilBreak.F; rw [OptionT.run, (dw.bodyDecreases s).choose_spec]
    simp
    congr
    ext sub
    cases sub with | mk p h =>
    cases p with | mk a s =>
    cases a <;> rfl

/--
Loop unrolling lemma for `extrinsicLoopUntilBreak`.
-/
noncomputable def extrinsicLoopUntilBreak_eq {σ : Type u} {m : Type u → Type v} {rel : σ → σ → Prop}
    [Monad m] [LawfulMonad m]
    (body : PUnit → OptionT (StateT σ m) PUnit)
    (dw : LoopUntilBreak rel body)
    : extrinsicLoopUntilBreak body = discard (do body ⟨⟩; liftM (extrinsicLoopUntilBreak body)).run := by
  open Std.Internal in
  ext s
  unfold extrinsicLoopUntilBreak
  simp only [StateT.run, bind_pure_comp, discard, Functor.mapConst, OptionT.run,
    bind, OptionT.bind, OptionT.mk, Function.comp_apply, StateT.map, StateT.bind,
    Function.const_apply, map_bind]
  let inst (s : σ) : Nonempty (m (PUnit × σ)) := ⟨pure (PUnit.unit, s)⟩
  let prf := Std.Internal.TerminatesTotally.ofLoopUntilBreak body dw
  conv => lhs; rw [@Std.Internal.extrinsicFix_eq _ _ (fun s => ⟨pure (PUnit.unit, s)⟩) _ prf]
  unfold extrinsicLoopUntilBreak.F
  congr
  ext p
  cases p with | mk a s =>
  cases a
  · simp [pure, StateT.pure]
  · simp [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, Functor.map, StateT.map]

/--
Loop unrolling lemma for `intrinsicLoopUntilBreak`.
-/
noncomputable def loopUntilBreak_eq {σ : Type u} {m : Type u → Type v} {rel : σ → σ → Prop}
    [Monad m] [LawfulMonad m]
    (body : PUnit → OptionT (StateT σ m) PUnit)
    (dw : LoopUntilBreak rel body)
    : intrinsicLoopUntilBreak body dw = discard (do body ⟨⟩; liftM (intrinsicLoopUntilBreak body dw)).run :=
  extrinsicLoopUntilBreak_eq body dw

/--
Construct a `LoopUntilBreak` proof from a measure function and a
-/
def LoopUntilBreak.ofMeasure [Monad m] {body : PUnit → OptionT (StateT σ m) PUnit}
    (f : σ → Nat) (bodyDecreases : ∀ s, DecreasesOn (fun _ => (measure f).rel) (body ⟨⟩) s)
    : LoopUntilBreak (measure f).rel body where
  wf := (measure f).wf
  bodyDecreases := bodyDecreases

theorem DecreasesOn.of_WP {σ m α} {rel : α → σ → σ → Prop} [Monad m] [WPAttach m ps] {prog : OptionT (StateT σ m) α}
    (h : ∀ s, ⦃fun preS => ⌜preS = s⌝⦄ prog ⦃(fun a s' => ⌜rel a s' s⌝, fun _ => ⌜True⌝, ExceptConds.false)⦄) :
    ∀ s, DecreasesOn rel prog s := by
  intro s
  apply WPAttach.attach
  have h := h s s
  simp [WP.wp] at h
  apply SPred.entails.trans h
  apply SPred.bientails.mp
  apply SPred.bientails.of_eq
  congr; ext x
  cases x with
  | mk a s =>
  cases a <;> grind

def sqrtBinary (x : Nat) : Nat := Id.run do
  let mut l := 0
  let mut r := x + 1
  -- Elaboration of `while 1 < r - l decreasing r - l do ...`
  -- `decreasing r - l` elaborates to the `decreasingMeasure` binding below.
  -- ?prf is an obligation to be solved by the user/automation.
  (_, (l, r)) ← flip StateT.run (l, r) do
    intrinsicLoopUntilBreak (fun _ => do
      let mut (l, r) ← get
      if r - l ≤ 1 then failure -- failure = break
      let m := (l + r) / 2
      if m * m > x then
        r := m
      else
        l := m
      set (l, r)) (LoopUntilBreak.ofMeasure (fun (l, r) => r - l) ?prf)
  return l
where finally
  case prf =>
    apply DecreasesOn.of_WP
    intro (l, r)
    mvcgen with (simp_wf; decreasing_tactic)

/-- info: 6 -/
#guard_msgs (info) in
#eval sqrtBinary 42

example : sqrtBinary 42 = 6 := by
  unfold sqrtBinary
  rw [loopUntilBreak_eq]
  rw [loopUntilBreak_eq]
  rw [loopUntilBreak_eq]
  rw [loopUntilBreak_eq]
  rw [loopUntilBreak_eq]
  rw [loopUntilBreak_eq]
  rfl

/-
def sqrtBinaryIdealized (x : Nat) : Nat := Id.run do
  let mut l := 0
  let mut r := x + 1
  while 1 < r - l
  decreasing r - l do
    if r - l ≤ 1 then break
    let m := (l + r) / 2
    if m * m > x then
      r := m
    else
      l := m
  return l
-/
where finally
  case prf =>
    apply DecreasesOn.of_WP
    intro (l, r)
    mvcgen
    case vc1 => simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel]; grind
    case vc2 => simp only [WellFoundedRelation.rel, InvImage, Nat.lt_wfRel]; grind

    /-
    dsimp
    intro s
    apply DecreasesOn.ite
    · apply DecreasesOn.bind_left DecreasesOn.failure
    · apply DecreasesOn.bind_right
      intro _ s
      apply DecreasesOn.get_then
      apply DecreasesOn.ite
      · apply DecreasesOn.bind_right
        intro _ _
        apply DecreasesOn.set
        apply Relation.TransGen.single _
        grind

      intro (l, r)
      apply DecreasesOn.ite
      · apply DecreasesOn.bind_right
        intro _


    have app_ite {m} {α σ} {c : Prop} [Decidable c] {t e : OptionT (StateT σ m) α} {s : σ} : (ite c t e) s = ite c (t s) (e s) := by split <;> rfl
    simp [Bind.bind, Pure.pure, Functor.map, OptionT.bind, OptionT.pure, OptionT.mk, StateT.bind, StateT.pure, StateT.get, StateT.set, app_ite]
    exists ?f'
    rotate_left
    intro l r
    simp [ite_apply]
-/
theorem DecreasesOn.ite [Decidable c] [Monad m] (ht : DecreasesOn rel t s) (he : DecreasesOn rel e s) :
    DecreasesOn (m:=m) rel (if c then t else e) s := by
  split <;> assumption

theorem DecreasesOn.bind_left {b : α → OptionT (StateT σ m) β} [Monad m] [LawfulMonad m]
    (h : DecreasesOn rel a s) : DecreasesOn (m:=m) rel (do let x ← a; b x) s := sorry

theorem DecreasesOn.bind_congr_right {b : α → OptionT (StateT σ m) β} {c : α → β → OptionT (StateT σ m) γ} [Monad m] [LawfulMonad m]
    (h : ∀ y, DecreasesOn (m:=m) rel (do let x ← a; c x y) s) : DecreasesOn (m:=m) rel (do let x ← a; let y ← b x; c x y) s := sorry

theorem DecreasesOn.bind_right {b : α → OptionT (StateT σ m) β} [Monad m] [LawfulMonad m]
    (h : ∀ x s', DecreasesOn rel (b x) s') : DecreasesOn (m:=m) rel (do let x ← a; b x) s := sorry

theorem DecreasesOn.failure [Monad m] [LawfulMonad m] :
    DecreasesOn (α := α) (m:=m) rel failure s := by
  exists pure (Subtype.mk (none, s) (by simp))
  simp [Alternative.failure, OptionT.fail, OptionT.mk, Pure.pure, StateT.pure]

theorem DecreasesOn.modify [Monad m] [LawfulMonad m] {rel : σ → σ → Prop} {f : σ → σ} (h : rel (f s) s) :
    DecreasesOn (m:=m) rel (modify f) s := by
  exists pure (Subtype.mk (some ⟨⟩, f s) (.inr (.single h)))
  simp only [_root_.modify, modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift,
    OptionT.lift, OptionT.mk, bind, StateT.bind, StateT.modifyGet, pure, StateT.pure,
    bind_pure_comp, map_pure]

theorem DecreasesOn.get_then [Monad m] [LawfulMonad m] {rel : σ → σ → Prop}
    {k : σ → OptionT (StateT σ m) α}
    (h : DecreasesOn rel (k s) s) : DecreasesOn (m:=m) rel (do let s ← get; k s) s:= by
  sorry

theorem DecreasesOn.set [Monad m] [LawfulMonad m] {rel : σ → σ → Prop} (h : rel s' s) :
    DecreasesOn (m:=m) rel (set s') s := by
  exists pure (Subtype.mk (some ⟨⟩, s') (.inr (.single h)))
  simp only [MonadStateOf.set, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk,
    bind, StateT.bind, StateT.set, pure, StateT.pure, bind_pure_comp, map_pure]

/-
import Std.Data.Iterators
import Std.Tactic.Do

open Std.Iterators
open Std.Do


def Iterator.step
    [Monad m]
    (step : Unit → β → m (ForInStep β))
    (measure : β → Nat)
    (it : IterM (α := β) m Unit) :
    m (IterStep (IterM (α := β) m Unit) Unit) := do
  match ← step () it.internalState with
  | ForInStep.done b => .done
  | ForInStep.yield next =>
    if measure next < measure it.internalState then
      .yield ⟨⟨next, it.internalState.upperBound⟩⟩ next
    else
      .done



-/

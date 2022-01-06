/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Meta.DiscrTree
import Lean.Meta.AppBuilder
import Lean.Meta.Eqns
import Lean.Meta.Tactic.AuxLemma
namespace Lean.Meta

/--
  The fields `levelParams` and `proof` are used to encode the proof of the simp lemma.
  If the `proof` is a global declaration `c`, we store `Expr.const c []` at `proof` without the universe levels, and `levelParams` is set to `#[]`
  When using the lemma, we create fresh universe metavariables.
  Motivation: most simp lemmas are global declarations, and this approach is faster and saves memory.

  The field `levelParams` is not empty only when we elaborate an expression provided by the user, and it contains universe metavariables.
  Then, we use `abstractMVars` to abstract the universe metavariables and create new fresh universe parameters that are stored at the field `levelParams`.
-/
structure SimpLemma where
  keys        : Array DiscrTree.Key := #[]
  levelParams : Array Name := #[] -- non empty for local universe polymorphic proofs.
  proof       : Expr
  priority    : Nat  := eval_prio default
  post        : Bool := true
  perm        : Bool := false -- true is lhs and rhs are identical modulo permutation of variables
  name?       : Option Name := none -- for debugging and tracing purposes
  deriving Inhabited

def SimpLemma.getName (s : SimpLemma) : Name :=
  match s.name? with
  | some n => n
  | none   => "<unknown>"

instance : ToFormat SimpLemma where
  format s :=
    let perm := if s.perm then ":perm" else ""
    let name := format s.getName
    let prio := f!":{s.priority}"
    name ++ prio ++ perm

instance : ToMessageData SimpLemma where
  toMessageData s := format s

instance : BEq SimpLemma where
  beq e₁ e₂ := e₁.proof == e₂.proof

structure SimpLemmas where
  pre          : DiscrTree SimpLemma := DiscrTree.empty
  post         : DiscrTree SimpLemma := DiscrTree.empty
  lemmaNames   : Std.PHashSet Name := {}
  toUnfold     : Std.PHashSet Name := {}
  erased       : Std.PHashSet Name := {}
  toUnfoldThms : Std.PHashMap Name (Array Name) := {}
  deriving Inhabited

def addSimpLemmaEntry (d : SimpLemmas) (e : SimpLemma) : SimpLemmas :=
  if e.post then
    { d with post := d.post.insertCore e.keys e, lemmaNames := updateLemmaNames d.lemmaNames }
  else
    { d with pre := d.pre.insertCore e.keys e, lemmaNames := updateLemmaNames d.lemmaNames }
where
  updateLemmaNames (s : Std.PHashSet Name) : Std.PHashSet Name :=
    match e.name? with
    | none => s
    | some name => s.insert name

def SimpLemmas.addDeclToUnfoldCore (d : SimpLemmas) (declName : Name) : SimpLemmas :=
  { d with toUnfold := d.toUnfold.insert declName }

/-- Return `true` if `declName` is tagged to be unfolded using `unfoldDefinition?` (i.e., without using equational theorems). -/
def SimpLemmas.isDeclToUnfold (d : SimpLemmas) (declName : Name) : Bool :=
  d.toUnfold.contains declName

def SimpLemmas.isLemma (d : SimpLemmas) (declName : Name) : Bool :=
  d.lemmaNames.contains declName

/-- Register the equational theorems for the given definition. -/
def SimpLemmas.registerDeclToUnfoldThms (d : SimpLemmas) (declName : Name) (eqThms : Array Name) : SimpLemmas :=
  { d with toUnfoldThms := d.toUnfoldThms.insert declName eqThms }

partial def SimpLemmas.eraseCore (d : SimpLemmas) (declName : Name) : SimpLemmas :=
  let d := { d with erased := d.erased.insert declName, lemmaNames := d.lemmaNames.erase declName, toUnfold := d.toUnfold.erase declName }
  if let some thms := d.toUnfoldThms.find? declName then
    thms.foldl (init := d) eraseCore
  else
    d

def SimpLemmas.erase [Monad m] [MonadError m] (d : SimpLemmas) (declName : Name) : m SimpLemmas := do
  unless d.isLemma declName || d.isDeclToUnfold declName || d.toUnfoldThms.contains declName do
    throwError "'{declName}' does not have [simp] attribute"
  d.eraseCore declName

private partial def isPerm : Expr → Expr → MetaM Bool
  | Expr.app f₁ a₁ _, Expr.app f₂ a₂ _ => isPerm f₁ f₂ <&&> isPerm a₁ a₂
  | Expr.mdata _ s _, t => isPerm s t
  | s, Expr.mdata _ t _ => isPerm s t
  | s@(Expr.mvar ..), t@(Expr.mvar ..) => isDefEq s t
  | Expr.forallE n₁ d₁ b₁ _, Expr.forallE n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.lam n₁ d₁ b₁ _, Expr.lam n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.letE n₁ t₁ v₁ b₁ _, Expr.letE n₂ t₂ v₂ b₂ _ =>
    isPerm t₁ t₂ <&&> isPerm v₁ v₂ <&&> withLetDecl n₁ t₁ v₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.proj _ i₁ b₁ _, Expr.proj _ i₂ b₂ _ => i₁ == i₂ <&&> isPerm b₁ b₂
  | s, t => s == t

private partial def shouldPreprocess (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs result => return !result.isEq

private partial def preprocess (e type : Expr) (inv : Bool) : MetaM (List (Expr × Expr)) := do
  let type ← whnf type
  if type.isForall then
    forallTelescopeReducing type fun xs type => do
      let e := mkAppN e xs
      let ps ← preprocess e type inv
      ps.mapM fun (e, type) =>
        return (← mkLambdaFVars xs e, ← mkForallFVars xs type)
  else if let some (_, lhs, rhs) := type.eq? then
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm e
      return [(e, type)]
    else
      return [(e, type)]
  else if let some (lhs, rhs) := type.iff? then
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm (← mkPropExt e)
      return [(e, type)]
    else
      let type ← mkEq lhs rhs
      let e    ← mkPropExt e
      return [(e, type)]
  else if let some (_, lhs, rhs) := type.ne? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type ← mkEq (← mkEq lhs rhs) (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some p := type.not? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type ← mkEq p (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some (type₁, type₂) := type.and? then
    let e₁ := mkProj ``And 0 e
    let e₂ := mkProj ``And 1 e
    return (← preprocess e₁ type₁ inv) ++ (← preprocess e₂ type₂ inv)
  else
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'True'"
    let type ← mkEq type (mkConst ``True)
    let e    ← mkEqTrue e
    return [(e, type)]

private def checkTypeIsProp (type : Expr) : MetaM Unit :=
  unless (← isProp type) do
    throwError "invalid 'simp', proposition expected{indentExpr type}"

private def mkSimpLemmaCore (e : Expr) (levelParams : Array Name) (proof : Expr) (post : Bool) (prio : Nat) (name? : Option Name) : MetaM SimpLemma := do
  let type ← instantiateMVars (← inferType e)
  withNewMCtxDepth do
    let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
    let type ← whnfR type
    let (keys, perm) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none => throwError "unexpected kind of 'simp' theorem{indentExpr type}"
    return { keys := keys, perm := perm, post := post, levelParams := levelParams, proof := proof, name? := name?, priority := prio }

private def mkSimpLemmasFromConst (declName : Name) (post : Bool) (inv : Bool) (prio : Nat) : MetaM (Array SimpLemma) := do
  let cinfo ← getConstInfo declName
  let val := mkConst declName (cinfo.levelParams.map mkLevelParam)
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if inv || (← shouldPreprocess type) then
      let mut r := #[]
      for (val, type) in (← preprocess val type inv) do
        let auxName ← mkAuxLemma cinfo.levelParams type val
        r := r.push <| (← mkSimpLemmaCore (mkConst auxName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst auxName) post prio declName)
      return r
    else
      #[← mkSimpLemmaCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst declName) post prio declName]

inductive SimpEntry where
  | lemma    : SimpLemma → SimpEntry
  | toUnfold : Name → SimpEntry
  | toUnfoldThms : Name → Array Name → SimpEntry
  deriving Inhabited

abbrev SimpExtension := SimpleScopedEnvExtension SimpEntry SimpLemmas

def SimpExtension.getLemmas (ext : SimpExtension) : CoreM SimpLemmas :=
  return ext.getState (← getEnv)

def addSimpLemma (ext : SimpExtension) (declName : Name) (post : Bool) (inv : Bool) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let simpLemmas ← mkSimpLemmasFromConst declName post inv prio
  for simpLemma in simpLemmas do
    ext.add (SimpEntry.lemma simpLemma) attrKind

def mkSimpAttr (attrName : Name) (attrDescr : String) (ext : SimpExtension) : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
        let prio ← getAttrParamOptPrio stx[2]
        if (← isProp info.type) then
          addSimpLemma ext declName post (inv := false) attrKind prio
        else if info.hasValue then
          if hasSmartUnfoldingDecl (← getEnv) declName then
            ext.add (SimpEntry.toUnfold declName) attrKind
          else if let some eqns ← getEqnsFor? declName then
            for eqn in eqns do
              addSimpLemma ext eqn post (inv := false) attrKind prio
            ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
          else
            ext.add (SimpEntry.toUnfold declName) attrKind
        else
          throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"
      discard <| go.run {} {}
    erase := fun declName => do
      let s ← ext.getState (← getEnv)
      let s ← s.erase declName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }

def mkSimpExt (extName : Name) : IO SimpExtension :=
  registerSimpleScopedEnvExtension {
    name     := extName
    initial  := {}
    addEntry := fun d e =>
      match e with
      | SimpEntry.lemma e => addSimpLemmaEntry d e
      | SimpEntry.toUnfold n => d.addDeclToUnfoldCore n
      | SimpEntry.toUnfoldThms n thms => d.registerDeclToUnfoldThms n thms
  }

def registerSimpAttr (attrName : Name) (attrDescr : String) (extName : Name := attrName.appendAfter "Ext") : IO SimpExtension := do
  let ext ← mkSimpExt extName
  mkSimpAttr attrName attrDescr ext
  return ext

builtin_initialize simpExtension : SimpExtension ← registerSimpAttr `simp "simplification theorem"

def getSimpLemmas : CoreM SimpLemmas :=
  simpExtension.getLemmas

/- Auxiliary method for adding a global declaration to a `SimpLemmas` datastructure. -/
def SimpLemmas.addConst (s : SimpLemmas) (declName : Name) (post : Bool := true) (inv : Bool := false) (prio : Nat := eval_prio default) : MetaM SimpLemmas := do
  let s := { s with erased := s.erased.erase declName }
  let simpLemmas ← mkSimpLemmasFromConst declName post inv prio
  return simpLemmas.foldl addSimpLemmaEntry s

def SimpLemma.getValue (simpLemma : SimpLemma) : MetaM Expr := do
  if simpLemma.proof.isConst && simpLemma.levelParams.isEmpty then
    let info ← getConstInfo simpLemma.proof.constName!
    if info.levelParams.isEmpty then
      return simpLemma.proof
    else
      return simpLemma.proof.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  else
    let us ← simpLemma.levelParams.mapM fun _ => mkFreshLevelMVar
    simpLemma.proof.instantiateLevelParamsArray simpLemma.levelParams us

private def preprocessProof (val : Expr) (inv : Bool) : MetaM (Array Expr) := do
  let type ← inferType val
  checkTypeIsProp type
  let ps ← preprocess val type inv
  return ps.toArray.map fun (val, _) => val

/- Auxiliary method for creating simp lemmas from a proof term `val`. -/
def mkSimpLemmas (levelParams : Array Name) (proof : Expr) (post : Bool := true) (inv : Bool := false) (prio : Nat := eval_prio default) (name? : Option Name := none): MetaM (Array SimpLemma) :=
  withReducible do
    (← preprocessProof proof inv).mapM fun val => mkSimpLemmaCore val levelParams val post prio name?

/- Auxiliary method for adding a local simp lemma to a `SimpLemmas` datastructure. -/
def SimpLemmas.add (s : SimpLemmas) (levelParams : Array Name) (proof : Expr) (inv : Bool := false) (post : Bool := true) (prio : Nat := eval_prio default) (name? : Option Name := none): MetaM SimpLemmas := do
  if proof.isConst then
    s.addConst proof.constName! post inv prio
  else
    let simpLemmas ← mkSimpLemmas levelParams proof post inv prio (← getName? proof)
    return simpLemmas.foldl addSimpLemmaEntry s
where
  getName? (e : Expr) : MetaM (Option Name) := do
    match name? with
    | some _ => return name?
    | none   =>
      let f := e.getAppFn
      if f.isConst then
        return f.constName!
      else if f.isFVar then
        let localDecl ← getFVarLocalDecl f
        return localDecl.userName
      else
        return none

def SimpLemmas.addDeclToUnfold (d : SimpLemmas) (declName : Name) : MetaM SimpLemmas := do
  if hasSmartUnfoldingDecl (← getEnv) declName then
    return d.addDeclToUnfoldCore declName
  else withLCtx {} {} do
    if let some eqns ← getEqnsFor? declName then
      let mut d := d
      for eqn in eqns do
        d ← SimpLemmas.addConst d eqn
      return d
    else
      return d.addDeclToUnfoldCore declName

end Lean.Meta

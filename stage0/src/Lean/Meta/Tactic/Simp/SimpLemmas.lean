/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Meta.LevelDefEq
import Lean.Meta.DiscrTree
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.AuxLemma
namespace Lean.Meta

structure SimpLemma where
  keys     : Array DiscrTree.Key
  val      : Expr
  priority : Nat
  post     : Bool
  perm     : Bool -- true is lhs and rhs are identical modulo permutation of variables
  name?    : Option Name := none -- for debugging and tracing purposes
  deriving Inhabited

def SimpLemma.getName (s : SimpLemma) : Name :=
  match s.name? with
  | some n => n
  | none   => "<unknown>"

instance : ToFormat SimpLemma where
  format s :=
    let perm := if s.perm then ":perm" else ""
    let name := fmt s.getName
    let prio := f!":{s.priority}"
    name ++ prio ++ perm

instance : ToMessageData SimpLemma where
  toMessageData s := fmt s

instance : BEq SimpLemma where
  beq e₁ e₂ := e₁.val == e₂.val

structure SimpLemmas where
  pre         : DiscrTree SimpLemma := DiscrTree.empty
  post        : DiscrTree SimpLemma := DiscrTree.empty
  lemmaNames  : Std.PHashSet Name := {}
  toUnfold    : Std.PHashSet Name := {}
  erased      : Std.PHashSet Name := {}
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

def SimpLemmas.addDeclToUnfold (d : SimpLemmas) (declName : Name) : SimpLemmas :=
  { d with toUnfold := d.toUnfold.insert declName }

def SimpLemmas.isDeclToUnfold (d : SimpLemmas) (declName : Name) : Bool :=
  d.toUnfold.contains declName

def SimpLemmas.isLemma (d : SimpLemmas) (declName : Name) : Bool :=
  d.lemmaNames.contains declName

def SimpLemmas.eraseCore [Monad m] [MonadError m] (d : SimpLemmas) (declName : Name) : m SimpLemmas := do
  return { d with erased := d.erased.insert declName, lemmaNames := d.lemmaNames.erase declName, toUnfold := d.toUnfold.erase declName }

def SimpLemmas.erase [Monad m] [MonadError m] (d : SimpLemmas) (declName : Name) : m SimpLemmas := do
  unless d.isLemma declName || d.isDeclToUnfold declName do
    throwError "'{declName}' does not have [simp] attribute"
  d.eraseCore declName

inductive SimpEntry where
  | lemma    : SimpLemma → SimpEntry
  | toUnfold : Name → SimpEntry
  deriving Inhabited

builtin_initialize simpExtension : SimpleScopedEnvExtension SimpEntry SimpLemmas ←
  registerSimpleScopedEnvExtension {
    name     := `simpExt
    initial  := {}
    addEntry := fun d e =>
      match e with
      | SimpEntry.lemma e => addSimpLemmaEntry d e
      | SimpEntry.toUnfold n => d.addDeclToUnfold n
  }

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

private partial def preprocess (e type : Expr) : MetaM (List (Expr × Expr)) := do
  let type ← whnf type
  if type.isForall then
    forallTelescopeReducing type fun xs type => do
      let e := mkAppN e xs
      let ps ← preprocess e type
      ps.mapM fun (e, type) =>
        return (← mkLambdaFVars xs e, ← mkForallFVars xs type)
  else if type.isEq then
    return [(e, type)]
  else if let some (lhs, rhs) := type.iff? then
    let type ← mkEq lhs rhs
    let e    ← mkPropExt e
    return [(e, type)]
  else if let some (_, lhs, rhs) := type.ne? then
    let type ← mkEq (← mkEq lhs rhs) (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some p := type.not? then
    let type ← mkEq p (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some (type₁, type₂) := type.and? then
    let e₁ := mkProj ``And 0 e
    let e₂ := mkProj ``And 1 e
    return (← preprocess e₁ type₁) ++ (← preprocess e₂ type₂)
  else
    let type ← mkEq type (mkConst ``True)
    let e    ← mkEqTrue e
    return [(e, type)]

private def checkTypeIsProp (type : Expr) : MetaM Unit :=
  unless (← isProp type) do
    throwError "invalid 'simp', proposition expected{indentExpr type}"

def mkSimpLemmaCore (e : Expr) (val : Expr) (post : Bool) (prio : Nat) (name? : Option Name) : MetaM SimpLemma := do
  let type ← instantiateMVars (← inferType e)
  withNewMCtxDepth do
    let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
    let (keys, perm) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none => throwError "unexpected kind of 'simp' lemma"
    return { keys := keys, perm := perm, post := post, val := val, name? := name?, priority := prio }

def mkSimpLemmasFromConst (declName : Name) (post : Bool) (prio : Nat) : MetaM (Array SimpLemma) := do
  let cinfo ← getConstInfo declName
  let val := mkConst declName (cinfo.levelParams.map mkLevelParam)
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if (← shouldPreprocess type) then
      let mut r := #[]
      for (val, type) in (← preprocess val type) do
        let auxName ← mkAuxLemma cinfo.levelParams type val
        r := r.push <| (← mkSimpLemmaCore (mkConst auxName (cinfo.levelParams.map mkLevelParam)) (mkConst auxName) post prio declName)
      return r
    else
      #[← mkSimpLemmaCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) (mkConst declName) post prio declName]

def addSimpLemma (declName : Name) (post : Bool) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let simpLemmas ← mkSimpLemmasFromConst declName post prio
  for simpLemma in simpLemmas do
    simpExtension.add (SimpEntry.lemma simpLemma) attrKind

builtin_initialize
  registerBuiltinAttribute {
    name  := `simp
    descr := "simplification lemma"
    add   := fun declName stx attrKind =>
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        if (← isProp info.type) then
          let post :=
            if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
          let prio ← getAttrParamOptPrio stx[2]
          addSimpLemma declName post attrKind prio
        else if info.hasValue then
          simpExtension.add (SimpEntry.toUnfold declName) attrKind
        else
          throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"
      discard <| go.run {} {}
    erase := fun declName => do
      let s ← simpExtension.getState (← getEnv)
      let s ← s.erase declName
      modifyEnv fun env => simpExtension.modifyState env fun _ => s
  }

def getSimpLemmas : MetaM SimpLemmas :=
  return simpExtension.getState (← getEnv)

/- Auxiliary method for adding a global declaration to a `SimpLemmas` datastructure. -/
def SimpLemmas.addConst (s : SimpLemmas) (declName : Name) (post : Bool := true) (prio : Nat := eval_prio default) : MetaM SimpLemmas := do
  let simpLemmas ← mkSimpLemmasFromConst declName post prio
  return simpLemmas.foldl addSimpLemmaEntry s

/- Auxiliary method for creating simp lemmas from a proof term `val`. -/
def mkSimpLemmas (val : Expr) (post : Bool := true) (prio : Nat := eval_prio default) (name? : Option Name := none): MetaM (Array SimpLemma) :=
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if (← shouldPreprocess type) then
      let mut r := #[]
      for (val, _) in (← preprocess val type) do
        r := r.push <| (← mkSimpLemmaCore val val post prio name?)
      return r
    else
      #[← mkSimpLemmaCore val val post prio name?]

/- Auxiliary method for adding a local simp lemma to a `SimpLemmas` datastructure. -/
def SimpLemmas.add (s : SimpLemmas) (e : Expr) (post : Bool := true) (prio : Nat := eval_prio default) (name? : Option Name := none): MetaM SimpLemmas := do
  if e.isConst then
    s.addConst e.constName! post prio
  else
    let simpLemmas ← mkSimpLemmas e post prio (← getName?)
    return simpLemmas.foldl addSimpLemmaEntry s
where
  getName? : MetaM (Option Name) := do
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

def SimpLemma.getValue (simpLemma : SimpLemma) : MetaM Expr := do
  match simpLemma.val with
  | Expr.const declName [] _ =>
    let info ← getConstInfo declName
    if info.levelParams.isEmpty then
      return simpLemma.val
    else
      return simpLemma.val.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  | _ => return simpLemma.val

end Lean.Meta

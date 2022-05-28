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
  The fields `levelParams` and `proof` are used to encode the proof of the simp theorem.
  If the `proof` is a global declaration `c`, we store `Expr.const c []` at `proof` without the universe levels, and `levelParams` is set to `#[]`
  When using the lemma, we create fresh universe metavariables.
  Motivation: most simp theorems are global declarations, and this approach is faster and saves memory.

  The field `levelParams` is not empty only when we elaborate an expression provided by the user, and it contains universe metavariables.
  Then, we use `abstractMVars` to abstract the universe metavariables and create new fresh universe parameters that are stored at the field `levelParams`.
-/
structure SimpTheorem where
  keys        : Array DiscrTree.Key := #[]
  /--
    It stores universe parameter names for universe polymorphic proofs.
    Recall that it is non-empty only when we elaborate an expression provided by the user.
    When `proof` is just a constant, we can use the universe parameter names stored in the declaration.
   -/
  levelParams : Array Name := #[]
  proof       : Expr
  priority    : Nat  := eval_prio default
  post        : Bool := true
  /-- `perm` is true if lhs and rhs are identical modulo permutation of variables. -/
  perm        : Bool := false
  /--
    `name?` is mainly relevant for producing trace messages.
    It is also viewed an `id` used to "erase" `simp` theorems from `SimpTheorems`.
  -/
  name?       : Option Name := none
  /-- `rfl` is true if `proof` is by `Eq.refl` or `rfl`. -/
  rfl         : Bool
  deriving Inhabited

def SimpTheorem.getName (s : SimpTheorem) : Name :=
  match s.name? with
  | some n => n
  | none   => "<unknown>"

mutual
  partial def isRflProofCore (type : Expr) (proof : Expr) : CoreM Bool := do
    match type with
    | .forallE _ _ type _ =>
      if let .lam _ _ proof _ := proof then
        isRflProofCore type proof
      else
        return false
    | _ =>
      if type.isAppOfArity ``Eq 3 then
        if proof.isAppOfArity ``Eq.refl 2 || proof.isAppOfArity ``rfl 2 then
          return true
        else if proof.isAppOfArity ``Eq.symm 4 then
          -- `Eq.symm` of rfl theorem is a rfl theorem
          isRflProofCore type proof.appArg! -- small hack: we don't need to set the exact type
        else if proof.isApp && proof.getAppFn.isConst then
          -- The application of a `rfl` theorem is a `rfl` theorem
          isRflTheorem proof.getAppFn.constName!
        else
          return false
      else
        return false

  partial def isRflTheorem (declName : Name) : CoreM Bool := do
    let .thmInfo info ← getConstInfo declName | return false
    isRflProofCore info.type info.value
end

def isRflProof (proof : Expr) : MetaM Bool := do
  if let .const declName .. := proof then
    isRflTheorem declName
  else
    isRflProofCore (← inferType proof) proof

instance : ToFormat SimpTheorem where
  format s :=
    let perm := if s.perm then ":perm" else ""
    let name := format s.getName
    let prio := f!":{s.priority}"
    name ++ prio ++ perm

instance : ToMessageData SimpTheorem where
  toMessageData s := format s

instance : BEq SimpTheorem where
  beq e₁ e₂ := e₁.proof == e₂.proof

structure SimpTheorems where
  pre          : DiscrTree SimpTheorem := DiscrTree.empty
  post         : DiscrTree SimpTheorem := DiscrTree.empty
  lemmaNames   : Std.PHashSet Name := {}
  toUnfold     : Std.PHashSet Name := {}
  erased       : Std.PHashSet Name := {}
  toUnfoldThms : Std.PHashMap Name (Array Name) := {}
  deriving Inhabited

def addSimpTheoremEntry (d : SimpTheorems) (e : SimpTheorem) : SimpTheorems :=
  if e.post then
    { d with post := d.post.insertCore e.keys e, lemmaNames := updateLemmaNames d.lemmaNames }
  else
    { d with pre := d.pre.insertCore e.keys e, lemmaNames := updateLemmaNames d.lemmaNames }
where
  updateLemmaNames (s : Std.PHashSet Name) : Std.PHashSet Name :=
    match e.name? with
    | none => s
    | some name => s.insert name

def SimpTheorems.addDeclToUnfoldCore (d : SimpTheorems) (declName : Name) : SimpTheorems :=
  { d with toUnfold := d.toUnfold.insert declName }

/-- Return `true` if `declName` is tagged to be unfolded using `unfoldDefinition?` (i.e., without using equational theorems). -/
def SimpTheorems.isDeclToUnfold (d : SimpTheorems) (declName : Name) : Bool :=
  d.toUnfold.contains declName

def SimpTheorems.isLemma (d : SimpTheorems) (declName : Name) : Bool :=
  d.lemmaNames.contains declName

/-- Register the equational theorems for the given definition. -/
def SimpTheorems.registerDeclToUnfoldThms (d : SimpTheorems) (declName : Name) (eqThms : Array Name) : SimpTheorems :=
  { d with toUnfoldThms := d.toUnfoldThms.insert declName eqThms }

partial def SimpTheorems.eraseCore (d : SimpTheorems) (declName : Name) : SimpTheorems :=
  let d := { d with erased := d.erased.insert declName, lemmaNames := d.lemmaNames.erase declName, toUnfold := d.toUnfold.erase declName }
  if let some thms := d.toUnfoldThms.find? declName then
    thms.foldl (init := d) eraseCore
  else
    d

def SimpTheorems.erase [Monad m] [MonadError m] (d : SimpTheorems) (declName : Name) : m SimpTheorems := do
  unless d.isLemma declName || d.isDeclToUnfold declName || d.toUnfoldThms.contains declName do
    throwError "'{declName}' does not have [simp] attribute"
  return d.eraseCore declName

private partial def isPerm : Expr → Expr → MetaM Bool
  | Expr.app f₁ a₁ _, Expr.app f₂ a₂ _ => isPerm f₁ f₂ <&&> isPerm a₁ a₂
  | Expr.mdata _ s _, t => isPerm s t
  | s, Expr.mdata _ t _ => isPerm s t
  | s@(Expr.mvar ..), t@(Expr.mvar ..) => isDefEq s t
  | Expr.forallE n₁ d₁ b₁ _, Expr.forallE n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.lam n₁ d₁ b₁ _, Expr.lam n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.letE n₁ t₁ v₁ b₁ _, Expr.letE n₂ t₂ v₂ b₂ _ =>
    isPerm t₁ t₂ <&&> isPerm v₁ v₂ <&&> withLetDecl n₁ t₁ v₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.proj _ i₁ b₁ _, Expr.proj _ i₂ b₂ _ => pure (i₁ == i₂) <&&> isPerm b₁ b₂
  | s, t => return s == t

private def checkBadRewrite (lhs rhs : Expr) : MetaM Unit := do
  let lhs ← DiscrTree.whnfDT lhs (root := true)
  if lhs == rhs && lhs.isFVar then
    throwError "invalid `simp` theorem, equation is equivalent to{indentExpr (← mkEq lhs rhs)}"

private partial def shouldPreprocess (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs result => do
    if let some (_, lhs, rhs) := result.eq? then
      checkBadRewrite lhs rhs
      return false
    else
      return true

private partial def preprocess (e type : Expr) (inv : Bool) (isGlobal : Bool) : MetaM (List (Expr × Expr)) :=
  go e type
where
  go (e type : Expr) : MetaM (List (Expr × Expr)) := do
  let type ← whnf type
  if type.isForall then
    forallTelescopeReducing type fun xs type => do
      let e := mkAppN e xs
      let ps ← go e type
      ps.mapM fun (e, type) =>
        return (← mkLambdaFVars xs e, ← mkForallFVars xs type)
  else if let some (_, lhs, rhs) := type.eq? then
    if isGlobal then
      checkBadRewrite lhs rhs
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm e
      return [(e, type)]
    else
      return [(e, type)]
  else if let some (lhs, rhs) := type.iff? then
    if isGlobal then
      checkBadRewrite lhs rhs
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
    if rhs.isConstOf ``Bool.true then
      return [(← mkAppM ``Bool.of_not_eq_true #[e], ← mkEq lhs (mkConst ``Bool.false))]
    else if rhs.isConstOf ``Bool.false then
      return [(← mkAppM ``Bool.of_not_eq_false #[e], ← mkEq lhs (mkConst ``Bool.true))]
    let type ← mkEq (← mkEq lhs rhs) (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some p := type.not? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    if let some (_, lhs, rhs) := p.eq? then
      if rhs.isConstOf ``Bool.true then
        return [(← mkAppM ``Bool.of_not_eq_true #[e], ← mkEq lhs (mkConst ``Bool.false))]
      else if rhs.isConstOf ``Bool.false then
        return [(← mkAppM ``Bool.of_not_eq_false #[e], ← mkEq lhs (mkConst ``Bool.true))]
    let type ← mkEq p (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some (type₁, type₂) := type.and? then
    let e₁ := mkProj ``And 0 e
    let e₂ := mkProj ``And 1 e
    return (← go e₁ type₁) ++ (← go e₂ type₂)
  else
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'True'"
    let type ← mkEq type (mkConst ``True)
    let e    ← mkEqTrue e
    return [(e, type)]

private def checkTypeIsProp (type : Expr) : MetaM Unit :=
  unless (← isProp type) do
    throwError "invalid 'simp', proposition expected{indentExpr type}"

private def mkSimpTheoremCore (e : Expr) (levelParams : Array Name) (proof : Expr) (post : Bool) (prio : Nat) (name? : Option Name) : MetaM SimpTheorem := do
  let type ← instantiateMVars (← inferType e)
  withNewMCtxDepth do
    let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
    let type ← whnfR type
    let (keys, perm) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none => throwError "unexpected kind of 'simp' theorem{indentExpr type}"
    return { keys, perm, post, levelParams, proof, name?, priority := prio, rfl := (← isRflProof proof) }

private def mkSimpTheoremsFromConst (declName : Name) (post : Bool) (inv : Bool) (prio : Nat) : MetaM (Array SimpTheorem) := do
  let cinfo ← getConstInfo declName
  let val := mkConst declName (cinfo.levelParams.map mkLevelParam)
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if inv || (← shouldPreprocess type) then
      let mut r := #[]
      for (val, type) in (← preprocess val type inv (isGlobal := true)) do
        let auxName ← mkAuxLemma cinfo.levelParams type val
        r := r.push <| (← mkSimpTheoremCore (mkConst auxName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst auxName) post prio declName)
      return r
    else
      return #[← mkSimpTheoremCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst declName) post prio declName]

inductive SimpEntry where
  | thm      : SimpTheorem → SimpEntry
  | toUnfold : Name → SimpEntry
  | toUnfoldThms : Name → Array Name → SimpEntry
  deriving Inhabited

abbrev SimpExtension := SimpleScopedEnvExtension SimpEntry SimpTheorems

def SimpExtension.getTheorems (ext : SimpExtension) : CoreM SimpTheorems :=
  return ext.getState (← getEnv)

def addSimpTheorem (ext : SimpExtension) (declName : Name) (post : Bool) (inv : Bool) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let simpThms ← mkSimpTheoremsFromConst declName post inv prio
  for simpThm in simpThms do
    ext.add (SimpEntry.thm simpThm) attrKind

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
          addSimpTheorem ext declName post (inv := false) attrKind prio
        else if info.hasValue then
          if let some eqns ← getEqnsFor? declName then
            for eqn in eqns do
              addSimpTheorem ext eqn post (inv := false) attrKind prio
            ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
            if hasSmartUnfoldingDecl (← getEnv) declName then
              ext.add (SimpEntry.toUnfold declName) attrKind
          else
            ext.add (SimpEntry.toUnfold declName) attrKind
        else
          throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"
      discard <| go.run {} {}
    erase := fun declName => do
      let s := ext.getState (← getEnv)
      let s ← s.erase declName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }

def mkSimpExt (extName : Name) : IO SimpExtension :=
  registerSimpleScopedEnvExtension {
    name     := extName
    initial  := {}
    addEntry := fun d e =>
      match e with
      | SimpEntry.thm e => addSimpTheoremEntry d e
      | SimpEntry.toUnfold n => d.addDeclToUnfoldCore n
      | SimpEntry.toUnfoldThms n thms => d.registerDeclToUnfoldThms n thms
  }

abbrev SimpExtensionMap := Std.HashMap Name SimpExtension

builtin_initialize simpExtensionMapRef : IO.Ref SimpExtensionMap ← IO.mkRef {}

def registerSimpAttr (attrName : Name) (attrDescr : String) (extName : Name := attrName.appendAfter "Ext") : IO SimpExtension := do
  let ext ← mkSimpExt extName
  mkSimpAttr attrName attrDescr ext -- Remark: it will fail if it is not performed during initialization
  simpExtensionMapRef.modify fun map => map.insert attrName ext
  return ext

builtin_initialize simpExtension : SimpExtension ← registerSimpAttr `simp "simplification theorem"

def getSimpExtension? (attrName : Name) : IO (Option SimpExtension) :=
  return (← simpExtensionMapRef.get).find? attrName

def getSimpTheorems : CoreM SimpTheorems :=
  simpExtension.getTheorems

/- Auxiliary method for adding a global declaration to a `SimpTheorems` datastructure. -/
def SimpTheorems.addConst (s : SimpTheorems) (declName : Name) (post : Bool := true) (inv : Bool := false) (prio : Nat := eval_prio default) : MetaM SimpTheorems := do
  let s := { s with erased := s.erased.erase declName }
  let simpThms ← mkSimpTheoremsFromConst declName post inv prio
  return simpThms.foldl addSimpTheoremEntry s

def SimpTheorem.getValue (simpThm : SimpTheorem) : MetaM Expr := do
  if simpThm.proof.isConst && simpThm.levelParams.isEmpty then
    let info ← getConstInfo simpThm.proof.constName!
    if info.levelParams.isEmpty then
      return simpThm.proof
    else
      return simpThm.proof.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  else
    let us ← simpThm.levelParams.mapM fun _ => mkFreshLevelMVar
    return simpThm.proof.instantiateLevelParamsArray simpThm.levelParams us

private def preprocessProof (val : Expr) (inv : Bool) : MetaM (Array Expr) := do
  let type ← inferType val
  checkTypeIsProp type
  let ps ← preprocess val type inv (isGlobal := false)
  return ps.toArray.map fun (val, _) => val

/- Auxiliary method for creating simp theorems from a proof term `val`. -/
def mkSimpTheorems (levelParams : Array Name) (proof : Expr) (post : Bool := true) (inv : Bool := false) (prio : Nat := eval_prio default) (name? : Option Name := none): MetaM (Array SimpTheorem) :=
  withReducible do
    (← preprocessProof proof inv).mapM fun val => mkSimpTheoremCore val levelParams val post prio name?

/- Auxiliary method for adding a local simp theorem to a `SimpTheorems` datastructure. -/
def SimpTheorems.add (s : SimpTheorems) (levelParams : Array Name) (proof : Expr) (inv : Bool := false) (post : Bool := true) (prio : Nat := eval_prio default) (name? : Option Name := none): MetaM SimpTheorems := do
  if proof.isConst then
    s.addConst proof.constName! post inv prio
  else
    let simpThms ← mkSimpTheorems levelParams proof post inv prio (← getName? proof)
    return simpThms.foldl addSimpTheoremEntry s
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

def SimpTheorems.addDeclToUnfold (d : SimpTheorems) (declName : Name) : MetaM SimpTheorems := do
  if let some eqns ← getEqnsFor? declName then
    let mut d := d
    for eqn in eqns do
      d ← SimpTheorems.addConst d eqn
    if hasSmartUnfoldingDecl (← getEnv) declName then
      d := d.addDeclToUnfoldCore declName
    return d
  else
    return d.addDeclToUnfoldCore declName

abbrev SimpTheoremsArray := Array SimpTheorems

def SimpTheoremsArray.addTheorem (thmsArray : SimpTheoremsArray) (h : Expr) (name? : Option Name := none) : MetaM SimpTheoremsArray :=
  if thmsArray.isEmpty then
    let thms : SimpTheorems := {}
    return #[ (← thms.add #[] h (name? := name?)) ]
  else
    thmsArray.modifyM 0 fun thms => thms.add #[] h (name? := name?)

def SimpTheoremsArray.eraseTheorem (thmsArray : SimpTheoremsArray) (thmId : Name) : SimpTheoremsArray :=
  thmsArray.map fun thms => thms.eraseCore thmId

def SimpTheoremsArray.isErased (thmsArray : SimpTheoremsArray) (thmId : Name) : Bool :=
  thmsArray.any fun thms => thms.erased.contains thmId

def SimpTheoremsArray.isDeclToUnfold (thmsArray : SimpTheoremsArray) (declName : Name) : Bool :=
  thmsArray.any fun thms => thms.isDeclToUnfold declName

macro "register_simp_attr" id:ident descr:str : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  `(initialize ext : SimpExtension ← registerSimpAttr $(quote id.getId) $descr
    syntax (name := $idParser:ident) $(quote str):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? (prio)? : attr)

end Meta

end Lean

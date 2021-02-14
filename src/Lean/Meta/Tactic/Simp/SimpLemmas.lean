/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Meta.LevelDefEq
import Lean.Meta.DiscrTree

namespace Lean.Meta

inductive SimpLemmaKind where
  | eq | iff | pos | neg
  deriving Inhabited, BEq

structure SimpLemma where
  keys     : Array DiscrTree.Key
  val      : Expr
  priority : Nat
  post     : Bool
  perm     : Bool -- true is lhs and rhs are identical modulo permutation of variables
  name?    : Option Name := none -- for debugging and tracing purposes
  kind     : SimpLemmaKind
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
  pre  : DiscrTree SimpLemma := DiscrTree.empty
  post : DiscrTree SimpLemma := DiscrTree.empty
  deriving Inhabited

def addSimpLemmaEntry (d : SimpLemmas) (e : SimpLemma) : SimpLemmas :=
  if e.post then
    { d with post := d.post.insertCore e.keys e }
  else
    { d with pre := d.pre.insertCore e.keys e }

builtin_initialize simpExtension : SimpleScopedEnvExtension SimpLemma SimpLemmas ←
  registerSimpleScopedEnvExtension {
    name     := `simpExt
    initial  := {}
    addEntry := addSimpLemmaEntry
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

def mkSimpLemmaCore (e : Expr) (val : Expr) (post : Bool) (prio : Nat) (name? : Option Name) : MetaM SimpLemma := do
  let type ← instantiateMVars (← inferType e)
  unless (← isProp type) do
    throwError! "invalid 'simp', proposition expected{indentExpr type}"
  withNewMCtxDepth do
    let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
    let (keys, perm, kind) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs, SimpLemmaKind.eq)
      | none =>
      match type.iff? with
      | some (lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs, SimpLemmaKind.iff)
      | none =>
      match type.not? with
      | some lhs => pure (← DiscrTree.mkPath lhs, false, SimpLemmaKind.neg)
      | none     => pure (← DiscrTree.mkPath type, false, SimpLemmaKind.pos)
    return { keys := keys, perm := perm, kind := kind, post := post, val := val, name? := name?, priority := prio }

def addSimpLemma (declName : Name) (post : Bool) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let cinfo ← getConstInfo declName
  /- The `simp` tactic uses fresh universe metavariables when using a global simp lemma.
     See `SimpLemma.getValue` -/
  let lemma ← mkSimpLemmaCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) (mkConst declName) post prio declName
  simpExtension.add lemma attrKind

builtin_initialize
  registerBuiltinAttribute {
    name  := `simp
    descr := "simplification lemma"
    add   := fun declName stx attrKind => do
      let post :=
        if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
      let prio ← getAttrParamOptPrio stx[2]
      discard <| addSimpLemma declName post attrKind prio |>.run {} {}
  }

def getSimpLemmas : MetaM SimpLemmas :=
  return simpExtension.getState (← getEnv)

/- Auxiliary method for creating a local simp lemma. -/
def mkSimpLemma (e : Expr) (post : Bool := true) (prio : Nat := evalPrio! default) (name? : Option Name := none) : MetaM SimpLemma := do
  mkSimpLemmaCore e e post prio name?

/- Auxiliary method for adding a local simp lemma to a `SimpLemmas` datastructure. -/
def SimpLemmas.add (s : SimpLemmas) (e : Expr) (post : Bool := true) (prio : Nat := evalPrio! default) (name? : Option Name := none) : MetaM SimpLemmas := do
  let lemma ← mkSimpLemma e post prio name?
  return addSimpLemmaEntry s lemma

/- Auxiliary method for adding a global declaration to a `SimpLemmas` datastructure. -/
def SimpLemmas.addConst (s : SimpLemmas) (declName : Name) (post : Bool := true) (prio : Nat := evalPrio! default) : MetaM SimpLemmas := do
  let cinfo ← getConstInfo declName
  let lemma ← mkSimpLemmaCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) (mkConst declName) post prio declName
  return addSimpLemmaEntry s lemma

def SimpLemma.getValue (lemma : SimpLemma) : MetaM Expr := do
  match lemma.val with
  | Expr.const declName [] _ =>
    let info ← getConstInfo declName
    if info.levelParams.isEmpty then
      return lemma.val
    else
      return lemma.val.updateConst! (← info.levelParams.mapM (fun _ => mkFreshLevelMVar))
  | _ => return lemma.val

end Lean.Meta

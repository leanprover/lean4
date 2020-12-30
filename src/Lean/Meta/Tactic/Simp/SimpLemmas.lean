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

structure SimpLemma where
  keys     : Array DiscrTree.Key
  val      : Expr
  priority : Nat
  post     : Bool
  perm     : Bool -- true is lhs and rhs are identical modulo permutation of variables
  name?    : Option Name := none -- for debugging and tracing purposes
  deriving Inhabited

instance : ToFormat SimpLemma where
  format s :=
    let perm := if s.perm then ":perm" else ""
    let name :=
      match s.name? with
      | some n => fmt n
      | none   => "<unknown>"
    let prio := f!":{s.priority}"
    name ++ prio ++ perm

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
  let type ← inferType e
  unless (← isProp type) do
    throwError! "invalid 'simp', proposition expected{indentExpr type}"
  withNewMCtxDepth do
    let (xs, _, type) ← forallMetaTelescopeReducing type
    let (keys, perm) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none =>
      match type.iff? with
      | some (lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none =>
        if type.isConstOf `False then
          if xs.size == 0 then
            throwError! "invalid 'simp', unexpected type{indentExpr type}"
          else
            pure (← DiscrTree.mkPath (← inferType xs.back), false)
        else
          pure (← DiscrTree.mkPath type, false)
    return { keys := keys, perm := perm, post := post, val := val, name? := name?, priority := prio }

def addSimpLemma (declName : Name) (post : Bool) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let cinfo ← getConstInfo declName
  /- The `simp` tactic uses fresh universe metavariables when using a global simp lemma. -/
  let lemma ← mkSimpLemmaCore (mkConst declName (cinfo.lparams.map mkLevelParam)) (mkConst declName) post prio declName
  simpExtension.add lemma attrKind
  pure ()

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

def getPreSimpLemmas : MetaM (DiscrTree SimpLemma) :=
  return simpExtension.getState (← getEnv) |>.pre

def getPostSimpLemmas : MetaM (DiscrTree SimpLemma) :=
  return simpExtension.getState (← getEnv) |>.post

/- Auxiliary method for creating a local simp lemma. -/
def mkSimpLemma (e : Expr) (post : Bool := true) (prio : Nat := evalPrio! default) (name? : Option Name := none) : MetaM SimpLemma := do
  mkSimpLemmaCore e e post prio name?

/- Auxiliary method for adding a local simp lemma to a `SimpLemmas` datastructure. -/
def SimpLemmas.add (s : SimpLemmas) (e : Expr) (post : Bool := true) (prio : Nat := evalPrio! default) (name? : Option Name := none) : MetaM SimpLemmas := do
  let lemma ← mkSimpLemma e post prio name?
  return addSimpLemmaEntry s lemma

end Lean.Meta

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Meta.Basic
import Lean.Meta.DiscrTree

namespace Lean.Meta

structure SimpLemma where
  keys        : Array DiscrTree.Key
  val         : Expr
  priority    : Nat
  globalName? : Option Name := none
  deriving Inhabited

instance : ToFormat SimpLemma where
  format s := match s.globalName? with
    | some n => fmt n
    | none   => "<local>"

instance : BEq SimpLemma where
  beq e₁ e₂ := e₁.val == e₂.val

structure SimpLemmas where
  discrTree       : DiscrTree SimpLemma := DiscrTree.empty
  deriving Inhabited

def addSimpLemmaEntry (d : SimpLemmas) (e : SimpLemma) : SimpLemmas :=
  { d with discrTree := d.discrTree.insertCore e.keys e }

builtin_initialize simpExtension : SimpleScopedEnvExtension SimpLemma SimpLemmas ←
  registerSimpleScopedEnvExtension {
    name     := `simpExt
    initial  := {}
    addEntry := addSimpLemmaEntry
  }

private def mkSimpLemmaKey (e : Expr) : MetaM (Array DiscrTree.Key) := do
  let type ← inferType e
  unless (← isProp type) do
    throwError! "invalid 'simp', proposition expected{indentExpr type}"
  withNewMCtxDepth do
    let (xs, _, type) ← forallMetaTelescopeReducing type
    match type.eq? with
    | some (_, lhs, _) => DiscrTree.mkPath lhs
    | none =>
    match type.iff? with
    | some (lhs, _) => DiscrTree.mkPath lhs
    | none =>
      if type.isConstOf `False then
        if xs.size == 0 then
          throwError! "invalid 'simp', unexpected type{indentExpr type}"
        else
          DiscrTree.mkPath (← inferType xs.back)
      else
        DiscrTree.mkPath type

def addSimpLemma (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let cinfo ← getConstInfo declName
  let c := mkConst declName (cinfo.lparams.map mkLevelParam)
  let keys ← mkSimpLemmaKey c
  simpExtension.add { keys := keys, val := c, priority := prio, globalName? := declName } attrKind
  pure ()

builtin_initialize
  registerBuiltinAttribute {
    name  := `simp
    descr := "simplification lemma"
    add   := fun declName stx attrKind => do
      let prio ← getAttrParamOptPrio stx[1]
      discard <| addSimpLemma declName attrKind prio |>.run {} {}
  }

def getSimpLemmas : MetaM (DiscrTree SimpLemma) :=
  return simpExtension.getState (← getEnv) |>.discrTree

end Lean.Meta

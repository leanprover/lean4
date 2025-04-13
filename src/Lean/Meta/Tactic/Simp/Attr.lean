/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta
open Simp

def mkSimpAttr (attrName : Name) (attrDescr : String) (ext : SimpExtension)
    (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref   := ref
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind => do
      if (← isSimproc declName <||> isBuiltinSimproc declName) then
        let simprocAttrName := simpAttrNameToSimprocAttrName attrName
        Attribute.add declName simprocAttrName stx attrKind
      else
        let go : MetaM Unit := do
          let info ← getAsyncConstInfo declName
          let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
          let inv := !stx[2].isNone
          let prio ← getAttrParamOptPrio stx[3]
          if (← isProp info.sig.get.type) then
            addSimpTheorem ext declName post (inv := inv) attrKind prio
          else if info.kind matches .defn then
            if inv then
              throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
            if (← SimpTheorems.ignoreEquations declName) then
              ext.add (SimpEntry.toUnfold declName) attrKind
            else if let some eqns ← getEqnsFor? declName then
              for eqn in eqns do
                addSimpTheorem ext eqn post (inv := false) attrKind prio
              ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
              if (← SimpTheorems.unfoldEvenWithEqns declName) then
                ext.add (SimpEntry.toUnfold declName) attrKind
            else
              ext.add (SimpEntry.toUnfold declName) attrKind
          else
            throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"
        discard <| go.run {} {}
    erase := fun declName => do
      if (← isSimproc declName <||> isBuiltinSimproc declName) then
        let simprocAttrName := simpAttrNameToSimprocAttrName attrName
        Attribute.erase declName simprocAttrName
      else
        let s := ext.getState (← getEnv)
        let s ← s.erase (.decl declName)
        modifyEnv fun env => ext.modifyState env fun _ => s
  }

/--
Registers the given name as a custom simp set. Applying the name as an attribute to a name adds it
to the simp set, and using the name as a parameter to the `simp` tactic causes `simp` to use the
included lemmas.

Custom simp sets must be registered during [initialization](lean-manual://section/initialization).

The description should be a short, singular noun phrase that describes the contents of the custom
simp set.
-/
def registerSimpAttr (attrName : Name) (attrDescr : String)
    (ref : Name := by exact decl_name%) : IO SimpExtension := do
  let ext ← mkSimpExt ref
  mkSimpAttr attrName attrDescr ext ref -- Remark: it will fail if it is not performed during initialization
  simpExtensionMapRef.modify fun map => map.insert attrName ext
  return ext

builtin_initialize simpExtension : SimpExtension ← registerSimpAttr `simp "simplification theorem"

builtin_initialize sevalSimpExtension : SimpExtension ← registerSimpAttr `seval "symbolic evaluator theorem"

def getSimpTheorems : CoreM SimpTheorems :=
  simpExtension.getTheorems

def getSEvalTheorems : CoreM SimpTheorems :=
  sevalSimpExtension.getTheorems

def Simp.Context.mkDefault : MetaM Context := do
  mkContext
    (config := {})
    (simpTheorems := #[(← Meta.getSimpTheorems)])
    (congrTheorems := (← Meta.getSimpCongrTheorems))

end Lean.Meta

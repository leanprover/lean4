/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Simp.Simproc
public section
namespace Lean.Meta
open Simp

/--
Marks `declName` to be unfolded in the given `SimpExtension`.
-/
def addDeclToUnfold (ext : SimpExtension) (declName : Name) (post inv : Bool) (prio : Nat) (attrKind : AttributeKind) : MetaM Bool := do
  if getOriginalConstKind? (← getEnv) declName == some .defn then
    if inv then
      throwError m!"Invalid `←` modifier: `{.ofConstName declName}` is a declaration name to be unfolded"
        ++ .note m!"The simplifier will automatically unfold definitions marked with the `[simp]` \
                    attribute, but it will not \"refold\" them"
    if (← Simp.ignoreEquations declName) then
      ext.add (SimpEntry.toUnfold declName) attrKind
    else if let some eqns ← getEqnsFor? declName then
      for eqn in eqns do
        addSimpTheorem ext eqn post (inv := false) attrKind prio
      ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
      if (← Simp.unfoldEvenWithEqns declName) then
        ext.add (SimpEntry.toUnfold declName) attrKind
    else
      ext.add (SimpEntry.toUnfold declName) attrKind
    return true
  else
    return false

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
          else unless (← addDeclToUnfold ext declName post inv prio attrKind) do
            throwError m!"Cannot add `simp` attribute to `{.ofConstName declName}`: It is not a proposition nor a definition (to unfold)"
              ++ .note m!"The `[simp]` attribute can be added to lemmas that should be automatically used by the simplifier \
                          and to definitions that the simplifier should automatically unfold"
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

/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Tactic.Simp.SimpTheorems -- for ignoreEquations
import Lean.Meta.Eqns -- for getEqnsFor?
public section
namespace Lean.Meta.Sym.Simp

/--
Adds a `Sym.Simp` theorem (an equality) to the given extension.
-/
def addSymSimpTheorem (ext : SymSimpExtension) (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let thm ← mkTheoremFromDecl declName
  ext.add thm attrKind

/--
Creates a `Sym.Simp` attribute for a named theorem set.
When a proposition is tagged, it is added as a rewrite theorem.
When a definition is tagged, its equation theorems are added.
-/
def mkSymSimpAttr (attrName : Name) (attrDescr : String) (ext : SymSimpExtension)
    (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref   := ref
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _ attrKind => do
      let go : MetaM Unit := do
        let info ← getAsyncConstInfo declName
        if (← isProp info.sig.get.type) then
          addSymSimpTheorem ext declName attrKind
        else if info.kind matches .defn then
          if (← Simp.ignoreEquations declName) then
            throwError "Cannot add `{attrName}` attribute to `{.ofConstName declName}`: \
              It is a reducible definition or projection. `Sym.simp` does not support unfolding."
          else if let some eqns ← getEqnsFor? declName then
            for eqn in eqns do
              addSymSimpTheorem ext eqn attrKind
          else
            throwError "Cannot add `{attrName}` attribute to `{.ofConstName declName}`: \
              No equation theorems found."
        else
          throwError "Cannot add `{attrName}` attribute to `{.ofConstName declName}`: \
            It is not a proposition nor a definition with equation theorems."
      discard <| go.run {} {}
    erase := fun _declName => do
      throwError "Erasing `Sym.simp` attributes is not supported yet."
  }

/--
Registers a named `Sym.Simp` theorem set. Each set gets its own attribute
and its own `SymSimpExtension` (persistent environment extension).

Must be called during initialization.
-/
def registerSymSimpAttr (attrName : Name) (attrDescr : String)
    (ref : Name := by exact decl_name%) : IO SymSimpExtension := do
  let ext ← mkSymSimpExt ref
  mkSymSimpAttr attrName attrDescr ext ref
  symSimpExtensionMapRef.modify fun map => map.insert attrName ext
  return ext

builtin_initialize symSimpExtension : SymSimpExtension ← registerSymSimpAttr `sym_simp "Sym.simp theorem"

def getSymSimpTheorems : CoreM Theorems :=
  symSimpExtension.getTheorems

end Lean.Meta.Sym.Simp

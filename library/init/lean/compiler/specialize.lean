/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.attributes
import init.lean.compiler.util

namespace Lean
namespace Compiler

inductive SpecializeAttributeKind
| specialize | nospecialize

namespace SpecializeAttributeKind

instance : Inhabited SpecializeAttributeKind := ⟨SpecializeAttributeKind.specialize⟩

protected def beq : SpecializeAttributeKind → SpecializeAttributeKind → Bool
| specialize, specialize => true
| nospecialize, nospecialize => true
| _, _ => false

instance : HasBeq SpecializeAttributeKind := ⟨SpecializeAttributeKind.beq⟩

end SpecializeAttributeKind

def mkSpecializeAttrs : IO (EnumAttributes SpecializeAttributeKind) :=
registerEnumAttributes `specializeAttrs
  [(`specialize, "mark definition to always be inlined", SpecializeAttributeKind.specialize),
   (`nospecialize, "mark definition to never be inlined", SpecializeAttributeKind.nospecialize) ]
  (fun env declName _ => checkIsDefinition env declName)

@[init mkSpecializeAttrs]
constant specializeAttrs : EnumAttributes SpecializeAttributeKind := default _

private partial def hasSpecializeAttrAux (env : Environment) (kind : SpecializeAttributeKind) : Name → Bool
| n => match specializeAttrs.getValue env n with
  | some k => kind == k
  | none   => if n.isInternal then hasSpecializeAttrAux n.getPrefix else false

@[export lean.has_specialize_attribute_core]
def hasSpecializeAttribute (env : Environment) (n : Name) : Bool :=
hasSpecializeAttrAux env SpecializeAttributeKind.specialize n

@[export lean.has_nospecialize_attribute_core]
def hasNospecializeAttribute (env : Environment) (n : Name) : Bool :=
hasSpecializeAttrAux env SpecializeAttributeKind.nospecialize n

inductive SpecArgKind
| fixed
| fixedNeutral -- computationally neutral
| fixedHO      -- higher order
| fixedInst    -- type class instance
| other

structure SpecInfo :=
(mutualDecls : List Name) (argKinds : SpecArgKind)

structure SpecState :=
(specInfo : SMap Name SpecInfo Name.quickLt := {})
(cache    : SMap Expr Name Expr.quickLt := {})

inductive SpecEntry
| info (name : Name) (info : SpecInfo)
| cache (key : Expr) (fn : Name)

namespace SpecState

instance : Inhabited SpecState := ⟨{}⟩

def addEntry (s : SpecState) (e : SpecEntry) : SpecState :=
match e with
| SpecEntry.info name info => { specInfo := s.specInfo.insert name info, .. s }
| SpecEntry.cache key fn   => { cache    := s.cache.insert key fn, .. s }

def switch : SpecState → SpecState
| ⟨m₁, m₂⟩ => ⟨m₁.switch, m₂.switch⟩

end SpecState

def mkSpecExtension : IO (SimplePersistentEnvExtension SpecEntry SpecState) :=
registerSimplePersistentEnvExtension {
  name          := `specialize,
  addEntryFn    := SpecState.addEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries SpecState.addEntry {} es).switch
}

@[init mkSpecExtension]
constant specExtension : SimplePersistentEnvExtension SpecEntry SpecState := default _

@[export lean.add_specialization_info_core]
def addSpecializationInfo (env : Environment) (fn : Name) (info : SpecInfo) : Environment :=
specExtension.addEntry env (SpecEntry.info fn info)

@[export lean.get_specialization_info_core]
def getSpecializationInfo (env : Environment) (fn : Name) : Option SpecInfo :=
(specExtension.getState env).specInfo.find fn

@[export lean.cache_specialization_core]
def cacheSpecialization (env : Environment) (e : Expr) (fn : Name) : Environment :=
specExtension.addEntry env (SpecEntry.cache e fn)

@[export lean.get_cached_specialization_core]
def getCachedSpecialization (env : Environment) (e : Expr) : Option Name :=
(specExtension.getState env).cache.find e

end Compiler
end Lean

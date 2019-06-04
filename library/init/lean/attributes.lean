/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment init.lean.parser.syntax

namespace Lean
open Lean.Parser

/- Scope management -/

structure ScopeManagerState :=
(allNamespaces : NameSet := {})
/- Stack of namespaces for each each open namespace and section  -/
(namespaces : List Name := [])
/- Stack of namespace/section headers -/
(headers : List Name := [])
(isNamespace : List Bool := [])

namespace ScopeManagerState

instance : Inhabited ScopeManagerState := ⟨{}⟩

def saveNamespace (s : ScopeManagerState) (n : Name) : ScopeManagerState :=
{ allNamespaces := s.allNamespaces.insert n, .. s }

end ScopeManagerState

def regScopeManagerExtension : IO (SimplePersistentEnvExtension Name ScopeManagerState) :=
registerSimplePersistentEnvExtension {
  name            := `scopes,
  addImportedFn   := λ as, mkStateFromImportedEntries ScopeManagerState.saveNamespace {} as,
  addEntryFn      := λ s n, { allNamespaces := s.allNamespaces.insert n, .. s },
}

@[init regScopeManagerExtension]
constant scopeManagerExt : SimplePersistentEnvExtension Name ScopeManagerState := default _

namespace Environment

def getNamespaces (env : Environment) : List Name :=
(scopeManagerExt.getState env).namespaces

def getNamespace (env : Environment) : Name :=
match env.getNamespaces with
| (n::_) := n
| _      := Name.anonymous

def getScopeHeader (env : Environment) : Name :=
match (scopeManagerExt.getState env).headers with
| (n::_) := n
| _      := Name.anonymous

def toValidNamespace (env : Environment) (n : Name) : Option Name :=
let s := scopeManagerExt.getState env in
if s.allNamespaces.contains n then some n
else s.namespaces.foldl
  (λ r ns, match r with
    | some _ := r
    | none   :=
      let c := ns ++ n in
      if s.allNamespaces.contains c then some c else none)
  none

end Environment


/-
structure AttributeEntry :=
(decl  : Name := default _)
(args  : Syntax := default _)
(scope : Option Name := none)
(nonLocal : Bool := false)

namespace AttributeEntry
instance : Inhabited AttributeEntry := ⟨{}⟩
end AttributeEntry

/- Create an array of entries to be saved on .olean file.
   We assume entries may contain duplicates, but we assume the one that occurs last is the most recent one. -/
def mkAttributeEntryArray (entries : List AttributeEntry) : Array AttributeEntry :=
let map : HashMap Name AttributeEntry := {} in
let map := entries.foldl (λ (map : HashMap Name AttributeEntry) entry, map.insert entry.decl entry) map in
let entries : Array AttributeEntry := map.fold (λ a k v, a.push v) Array.empty in
entries.qsort (λ a b, Name.quickLt a.decl b.decl)

structure AttributeState (σ : Type) :=
(importedEntries : Array (Array AttributeEntry))
(importedState   : Thunk σ)
(scopes          : List (List AttributeEntry × Option σ) := [])
(scopedEntries   : SMap Name AttributeEntry Name.quickLt := {})

structure AttributeDescr (σ : Type) :=
(name : Name)
(initState : σ)
(addEntryFn : Bool → AttributeEntry → σ → σ)
/- If `eraseEntryFn == some g`, then we can remove attributes -/
(eraseEntryFn : Option (AttributeEntry → σ → σ) := none)
/- If `updateEnvFn == some g`, then `g` is invoked whenever an attribute entry is activated. -/
(updateEnvFn : Option (AttributeEntry → Environment → Environment) := none)
/- If `nonLocalEntries == true`, then an attribute for a declaration `f` may be set in a module different from the module where `f` was declared. -/
(nonLocalEntries : Bool := false)
(scopedEntries : Bool := false)

structure AttributeExtension (σ : Type) :=
(descr : AttributeDescr σ)
(ext   : EnvExtension (AttributeState σ))

-/
end Lean

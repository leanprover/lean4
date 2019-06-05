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


namespace Environment

/- Return true iff `n` is the name of a registered attribute. -/
def isAttribute (env : Environment) (n : Name) : Bool :=
false -- TODO

/- Return the name of all registered attributes. -/
def getAttributes (env : Environment) : Array Name :=
Array.empty -- TODO

/- Add attribute `attr` to declaration `decl` with arguments `args`. If `persistent == true`, then attribute is saved on .olean file.
   It returns `Except.error` when
   - `decl` is not the name of a declaration in `env`.
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support `persistent == false`.
   - `args` is not valid for `attr`. -/
def addAttribute (env : Environment) (decl : Name) (attr : Name) (args : Syntax := Syntax.missing) (persistent := true) : ExceptT String Id Environment :=
pure env -- TODO

/- Add a scoped attribute `attr` to declaration `decl` with arguments `args` and scope `decl.getPrefix`.
   Scoped attributes are always persistent.
   It returns `Except.error` when
   - `decl` is not the name of a declaration in `env`.
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support scoped attributes.
   - `args` is not valid for `attr`.

   Remark: the attribute will not be activated if `decl` is not inside the current namespace `env.getNamespace`. -/
def addScopedAttribute (env : Environment) (decl : Name) (attr : Name) (args : Syntax := Syntax.missing) : ExceptT String Id Environment :=
pure env -- TODO

/- Remove attribute `attr` from declaration `decl`. The effect is the current scope.
   It returns `Except.error` when
   - `decl` is not the name of a declaration in `env`.
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support erasure.
   - `args` is not valid for `attr`. -/
def eraseAttribute (env : Environment) (decl : Name) (attr : Name) : ExceptT String Id Environment :=
pure env -- TODO

/- Activate the scoped attribute `attr` for all declarations in scope `scope`.
   We use this function to implement the command `open foo`. -/
def activateScopedAttribute (env : Environment) (attr : Name) (scope : Name) : Environment :=
env -- TODO

/- Activate all scoped attributes at `scope` -/
def activateScopedAttributes (env : Environment) (scope : Name) : Environment :=
let attrs := env.getAttributes in
attrs.foldl (λ env attr, env.activateScopedAttribute attr scope) env

/- We use this function to implement commands `namespace foo` and `section foo`.

   It activates scoped attributes in the new resulting namespace. -/
def pushScope (env : Environment) (header : Name) (isNamespace : Bool) : Environment :=
env -- TODO

/- We use this function to implement commands `end foo` for closing namespaces and sections. -/
def popScope (env : Environment) : Environment :=
env -- TODO

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

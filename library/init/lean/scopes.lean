/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean

/- Scope management

TODO: delete after we delete parser implemented in C++.
We have decided to store scope information at ElabState
-/

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
  addImportedFn   := fun as => mkStateFromImportedEntries ScopeManagerState.saveNamespace {} as,
  addEntryFn      := fun s n => { allNamespaces := s.allNamespaces.insert n, .. s },
}

@[init regScopeManagerExtension]
constant scopeManagerExt : SimplePersistentEnvExtension Name ScopeManagerState := default _

namespace Environment

@[export lean.get_namespaces_core]
def getNamespaces (env : Environment) : List Name :=
(scopeManagerExt.getState env).namespaces

def getNamespaceSet (env : Environment) : NameSet :=
(scopeManagerExt.getState env).allNamespaces

@[export lean.is_namespace_core]
def isNamespace (env : Environment) (n : Name) : Bool :=
env.getNamespaceSet.contains n

@[export lean.in_section_core]
def inSection (env : Environment) : Bool :=
match (scopeManagerExt.getState env).isNamespace with
| (b::_) => !b
| _      => false

@[export lean.has_open_scopes_core]
def hasOpenScopes (env : Environment) : Bool :=
!env.getNamespaces.isEmpty

@[export lean.get_namespace_core]
def getNamespace (env : Environment) : Name :=
match env.getNamespaces with
| (n::_) => n
| _      => Name.anonymous

@[export lean.get_scope_header_core]
def getScopeHeader (env : Environment) : Name :=
match (scopeManagerExt.getState env).headers with
| (n::_) => n
| _      => Name.anonymous

@[export lean.to_valid_namespace_core]
def toValidNamespace (env : Environment) (n : Name) : Option Name :=
let s := scopeManagerExt.getState env;
if s.allNamespaces.contains n then some n
else s.namespaces.foldl
  (fun r ns => match r with
    | some _ => r
    | none   =>
      let c := ns ++ n;
      if s.allNamespaces.contains c then some c else none)
  none

def registerNamespaceAux (env : Environment) (n : Name) : Environment :=
if env.getNamespaceSet.contains n then env else scopeManagerExt.addEntry env n

@[export lean.register_namespace_core]
def registerNamespace : Environment → Name → Environment
| env n@(Name.mkString p _) := registerNamespace (registerNamespaceAux env n) p
| env _ := env

def pushScopeCore (env : Environment) (header : Name) (isNamespace : Bool) : Environment :=
let ns    := env.getNamespace;
let newNs := if isNamespace then ns ++ header else ns;
let env   := env.registerNamespaceAux newNs;
let env   := scopeManagerExt.modifyState env $ fun s =>
  { headers     := header :: s.headers,
    namespaces  := newNs :: s.namespaces,
    isNamespace := isNamespace :: s.isNamespace,
    .. s };
env

def popScopeCore (env : Environment) : Environment :=
if env.getNamespaces.isEmpty then env
else scopeManagerExt.modifyState env $ fun s =>
  { headers     := s.headers.tail,
    namespaces  := s.namespaces.tail,
    isNamespace := s.isNamespace.tail,
    .. s }

end Environment
end Lean

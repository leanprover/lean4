/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean
def Syntax := Unit -- Temporary hack
def Syntax.missing := () -- Temporary hack

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
| (b::_) := !b
| _      := false

@[export lean.has_open_scopes_core]
def hasOpenScopes (env : Environment) : Bool :=
!env.getNamespaces.isEmpty

@[export lean.get_namespace_core]
def getNamespace (env : Environment) : Name :=
match env.getNamespaces with
| (n::_) := n
| _      := Name.anonymous

@[export lean.get_scope_header_core]
def getScopeHeader (env : Environment) : Name :=
match (scopeManagerExt.getState env).headers with
| (n::_) := n
| _      := Name.anonymous

@[export lean.to_valid_namespace_core]
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

def registerNamespaceAux (env : Environment) (n : Name) : Environment :=
if env.getNamespaceSet.contains n then env else scopeManagerExt.addEntry env n

@[export lean.register_namespace_core]
def registerNamespace : Environment → Name → Environment
| env n@(Name.mkString p _) := registerNamespace (registerNamespaceAux env n) p
| env _ := env

def pushScopeCore (env : Environment) (header : Name) (isNamespace : Bool) : Environment :=
let ns    := env.getNamespace in
let newNs := if isNamespace then ns ++ header else ns in
let env   := env.registerNamespaceAux newNs in
let env   := scopeManagerExt.modifyState env $ λ s,
  { headers     := header :: s.headers,
    namespaces  := newNs :: s.namespaces,
    isNamespace := isNamespace :: s.isNamespace,
    .. s } in
env

def popScopeCore (env : Environment) : Environment :=
if env.getNamespaces.isEmpty then env
else scopeManagerExt.modifyState env $ λ s,
  { headers     := s.headers.tail,
    namespaces  := s.namespaces.tail,
    isNamespace := s.isNamespace.tail,
    .. s }

end Environment

structure AttributeImpl :=
(name : Name)
(descr : String)
(add (env : Environment) (decl : Name) (args : Syntax) (persistent : Bool) : IO Environment)
(addScoped (env : Environment) (decl : Name) (args : Syntax) : IO Environment
           := throw (IO.userError ("attribute '" ++ toString name ++ "' does not support scopes")))
(erase (env : Environment) (decl : Name) (persistent : Bool) : IO Environment
       := throw (IO.userError ("attribute '" ++ toString name ++ "' does not support removal")))
(activateScoped (env : Environment) (scope : Name) : IO Environment := pure env)
(pushScope (env : Environment) : IO Environment := pure env)
(popScope (env : Environment) : IO Environment := pure env)

def mkAttributeMapRef : IO (IO.Ref (HashMap Name AttributeImpl)) :=
IO.mkRef {}

@[init mkAttributeMapRef]
constant attributeMapRef : IO.Ref (HashMap Name AttributeImpl) := default _

def mkAttributeArrayRef : IO (IO.Ref (Array AttributeImpl)) :=
IO.mkRef Array.empty

@[init mkAttributeArrayRef]
constant attributeArrayRef : IO.Ref (Array AttributeImpl) := default _

/- Low level attribute registration function. -/
def registerAttribute (attr : AttributeImpl) : IO Unit :=
do m ← attributeMapRef.get,
   when (m.contains attr.name) $ throw (IO.userError ("invalid attribute declaration, '" ++ toString attr.name ++ "' has already been used")),
   initializing ← IO.initializing,
   unless initializing $ throw (IO.userError ("failed to register attribute, attributes can only be registered during initialization")),
   attributeMapRef.modify (λ m, m.insert attr.name attr),
   attributeArrayRef.modify (λ attrs, attrs.push attr)

namespace Environment

/- Return true iff `n` is the name of a registered attribute. -/
def isAttribute (env : Environment) (n : Name) : IO Bool :=
do m ← attributeMapRef.get, pure (m.contains n)

/- Return the name of all registered attributes. -/
def getAttributeNames (env : Environment) : IO (List Name) :=
do m ← attributeMapRef.get, pure $ m.fold (λ r n _, n::r) []

def getAttributeImpl (env : Environment) (attrName : Name) : IO AttributeImpl :=
do m ← attributeMapRef.get,
   match m.find attrName with
   | some attr := pure attr
   | none      := throw (IO.userError ("unknown attribute '" ++ toString attrName ++ "'"))

/- Add attribute `attr` to declaration `decl` with arguments `args`. If `persistent == true`, then attribute is saved on .olean file.
   It throws an error when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support `persistent == false`.
   - `args` is not valid for `attr`. -/
def addAttribute (env : Environment) (decl : Name) (attrName : Name) (args : Syntax := Syntax.missing) (persistent := true) : IO Environment :=
do attr ← env.getAttributeImpl attrName,
   attr.add env decl args persistent

/- Add a scoped attribute `attr` to declaration `decl` with arguments `args` and scope `decl.getPrefix`.
   Scoped attributes are always persistent.
   It returns `Except.error` when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support scoped attributes.
   - `args` is not valid for `attr`.

   Remark: the attribute will not be activated if `decl` is not inside the current namespace `env.getNamespace`. -/
def addScopedAttribute (env : Environment) (decl : Name) (attrName : Name) (args : Syntax := Syntax.missing) : IO Environment :=
do attr ← env.getAttributeImpl attrName,
   attr.addScoped env decl args

/- Remove attribute `attr` from declaration `decl`. The effect is the current scope.
   It returns `Except.error` when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support erasure.
   - `args` is not valid for `attr`. -/
def eraseAttribute (env : Environment) (decl : Name) (attrName : Name) (persistent := true) : IO Environment :=
do attr ← env.getAttributeImpl attrName,
   attr.erase env decl persistent

/- Activate the scoped attribute `attr` for all declarations in scope `scope`.
   We use this function to implement the command `open foo`. -/
def activateScopedAttribute (env : Environment) (attrName : Name) (scope : Name) : IO Environment :=
do attr ← env.getAttributeImpl attrName,
   attr.activateScoped env scope

/- Activate all scoped attributes at `scope` -/
def activateScopedAttributes (env : Environment) (scope : Name) : IO Environment :=
do attrs ← attributeArrayRef.get,
   attrs.mfoldl (λ env attr, attr.activateScoped env scope) env

/- We use this function to implement commands `namespace foo` and `section foo`.
   It activates scoped attributes in the new resulting namespace. -/
@[export lean.push_scope_core]
def pushScope (env : Environment) (header : Name) (isNamespace : Bool) : IO Environment :=
do let env := env.pushScopeCore header isNamespace,
   let ns  := env.getNamespace,
   attrs ← attributeArrayRef.get,
   attrs.mfoldl (λ env attr, do env ← attr.pushScope env, if isNamespace then attr.activateScoped env ns else pure env) env

/- We use this function to implement commands `end foo` for closing namespaces and sections. -/
@[export lean.pop_scope_core]
def popScope (env : Environment) : IO Environment :=
do let env := env.popScopeCore,
   attrs ← attributeArrayRef.get,
   attrs.mfoldl (λ env attr, attr.popScope env) env

end Environment
end Lean

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

/- Low level attribute registration function. -/
def registerAttribute (attr : AttributeImpl) : IO Unit :=
do m ← attributeMapRef.get,
   when (m.contains attr.name) $ throw (IO.userError ("invalid attribute declaration, '" ++ toString attr.name ++ "' has already been used")),
   initializing ← IO.initializing,
   unless initializing $ throw (IO.userError ("failed to register attribute, attributes can only be registered during initialization")),
   attributeMapRef.modify (λ m, m.insert attr.name attr)

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
do m ← attributeMapRef.get,
   m.mfold (λ env _ attr, attr.activateScoped env scope) env

/- We use this function to implement commands `namespace foo` and `section foo`.
   It activates scoped attributes in the new resulting namespace. -/
def pushScope (env : Environment) (header : Name) (isNamespace : Bool) : IO Environment :=
pure env -- TODO

/- We use this function to implement commands `end foo` for closing namespaces and sections. -/
def popScope (env : Environment) : IO Environment :=
pure env -- TODO

end Environment

end Lean

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.scopes init.lean.syntax

namespace Lean

inductive AttributeApplicationTime
| afterTypeChecking | afterCompilation

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
(applicationTime := AttributeApplicationTime.afterTypeChecking)

instance AttributeImpl.inhabited : Inhabited AttributeImpl :=
⟨{ name := default _, descr := default _, add := fun env _ _ _ => pure env }⟩

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
do m ← attributeMapRef.get;
   when (m.contains attr.name) $ throw (IO.userError ("invalid attribute declaration, '" ++ toString attr.name ++ "' has already been used"));
   initializing ← IO.initializing;
   unless initializing $ throw (IO.userError ("failed to register attribute, attributes can only be registered during initialization"));
   attributeMapRef.modify (fun m => m.insert attr.name attr);
   attributeArrayRef.modify (fun attrs => attrs.push attr)

/- Return true iff `n` is the name of a registered attribute. -/
@[export lean_is_attribute]
def isAttribute (n : Name) : IO Bool :=
do m ← attributeMapRef.get; pure (m.contains n)

/- Return the name of all registered attributes. -/
def getAttributeNames : IO (List Name) :=
do m ← attributeMapRef.get; pure $ m.fold (fun r n _ => n::r) []

def getAttributeImpl (attrName : Name) : IO AttributeImpl :=
do m ← attributeMapRef.get;
   match m.find attrName with
   | some attr => pure attr
   | none      => throw (IO.userError ("unknown attribute '" ++ toString attrName ++ "'"))

@[export lean_attribute_application_time]
def attributeApplicationTime (n : Name) : IO AttributeApplicationTime :=
do attr ← getAttributeImpl n;
   pure attr.applicationTime

namespace Environment

/- Add attribute `attr` to declaration `decl` with arguments `args`. If `persistent == true`, then attribute is saved on .olean file.
   It throws an error when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support `persistent == false`.
   - `args` is not valid for `attr`. -/
@[export lean_add_attribute]
def addAttribute (env : Environment) (decl : Name) (attrName : Name) (args : Syntax := Syntax.missing) (persistent := true) : IO Environment :=
do attr ← getAttributeImpl attrName;
   attr.add env decl args persistent

/- Add a scoped attribute `attr` to declaration `decl` with arguments `args` and scope `decl.getPrefix`.
   Scoped attributes are always persistent.
   It returns `Except.error` when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support scoped attributes.
   - `args` is not valid for `attr`.

   Remark: the attribute will not be activated if `decl` is not inside the current namespace `env.getNamespace`. -/
@[export lean_add_scoped_attribute]
def addScopedAttribute (env : Environment) (decl : Name) (attrName : Name) (args : Syntax := Syntax.missing) : IO Environment :=
do attr ← getAttributeImpl attrName;
   attr.addScoped env decl args

/- Remove attribute `attr` from declaration `decl`. The effect is the current scope.
   It returns `Except.error` when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support erasure.
   - `args` is not valid for `attr`. -/
@[export lean_erase_attribute]
def eraseAttribute (env : Environment) (decl : Name) (attrName : Name) (persistent := true) : IO Environment :=
do attr ← getAttributeImpl attrName;
   attr.erase env decl persistent

/- Activate the scoped attribute `attr` for all declarations in scope `scope`.
   We use this function to implement the command `open foo`. -/
@[export lean_activate_scoped_attribute]
def activateScopedAttribute (env : Environment) (attrName : Name) (scope : Name) : IO Environment :=
do attr ← getAttributeImpl attrName;
   attr.activateScoped env scope

/- Activate all scoped attributes at `scope` -/
@[export lean_activate_scoped_attributes]
def activateScopedAttributes (env : Environment) (scope : Name) : IO Environment :=
do attrs ← attributeArrayRef.get;
   attrs.mfoldl (fun env attr => attr.activateScoped env scope) env

/- We use this function to implement commands `namespace foo` and `section foo`.
   It activates scoped attributes in the new resulting namespace. -/
@[export lean_push_scope]
def pushScope (env : Environment) (header : Name) (isNamespace : Bool) : IO Environment :=
do let env := env.pushScopeCore header isNamespace;
   let ns  := env.getNamespace;
   attrs ← attributeArrayRef.get;
   attrs.mfoldl (fun env attr => do env ← attr.pushScope env; if isNamespace then attr.activateScoped env ns else pure env) env

/- We use this function to implement commands `end foo` for closing namespaces and sections. -/
@[export lean_pop_scope]
def popScope (env : Environment) : IO Environment :=
do let env := env.popScopeCore;
   attrs ← attributeArrayRef.get;
   attrs.mfoldl (fun env attr => attr.popScope env) env

end Environment

/--
   Tag attributes are simple and efficient. They are useful for marking declarations in the modules where
   they were defined.

   The startup cost for this kind of attribute is very small since `addImportedFn` is a constant function.

   They provide the predicate `tagAttr.hasTag env decl` which returns true iff declaration `decl`
   is tagged in the environment `env`. -/
structure TagAttribute :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension Name NameSet)

def registerTagAttribute (name : Name) (descr : String) (validate : Environment → Name → Except String Unit := fun _ _ => Except.ok ()) : IO TagAttribute :=
do
ext : PersistentEnvExtension Name NameSet ← registerPersistentEnvExtension {
  name            := name,
  addImportedFn   := fun _ => pure {},
  addEntryFn      := fun (s : NameSet) n => s.insert n,
  exportEntriesFn := fun es =>
    let r : Array Name := es.fold (fun a e => a.push e) Array.empty;
    r.qsort Name.quickLt,
  statsFn         := fun s => "tag attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
};
let attrImpl : AttributeImpl := {
  name  := name,
  descr := descr,
  add   := fun env decl args persistent => do
    unless args.isMissing $ throw (IO.userError ("invalid attribute '" ++ toString name ++ "', unexpected argument"));
    unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString name ++ "', must be persistent"));
    unless (env.getModuleIdxFor decl).isNone $
      throw (IO.userError ("invalid attribute '" ++ toString name ++ "', declaration is in an imported module"));
    match validate env decl with
    | Except.error msg => throw (IO.userError ("invalid attribute '" ++ toString name ++ "', " ++ msg))
    | _                => pure $ ext.addEntry env decl
};
registerAttribute attrImpl;
pure { attr := attrImpl, ext := ext }

namespace TagAttribute

instance : Inhabited TagAttribute := ⟨{attr := default _, ext := default _}⟩

def hasTag (attr : TagAttribute) (env : Environment) (decl : Name) : Bool :=
match env.getModuleIdxFor decl with
| some modIdx => (attr.ext.getModuleEntries env modIdx).binSearchContains decl Name.quickLt
| none        => (attr.ext.getState env).contains decl

end TagAttribute

/--
   A `TagAttribute` variant where we can attach parameters to attributes.
   It is slightly more expensive and consumes a little bit more memory than `TagAttribute`.

   They provide the function `pAttr.getParam env decl` which returns `some p` iff declaration `decl`
   contains the attribute `pAttr` with parameter `p`. -/
structure ParametricAttribute (α : Type) :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension (Name × α) (NameMap α))

def registerParametricAttribute {α : Type} [Inhabited α] (name : Name) (descr : String)
       (getParam : Environment → Name → Syntax → Except String α)
       (afterSet : Environment → Name → α → Except String Environment := fun env _ _ => Except.ok env) : IO (ParametricAttribute α) :=
do
ext : PersistentEnvExtension (Name × α) (NameMap α) ← registerPersistentEnvExtension {
  name            := name,
  addImportedFn   := fun _ => pure {},
  addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2,
  exportEntriesFn := fun m =>
    let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) Array.empty;
    r.qsort (fun a b => Name.quickLt a.1 b.1),
  statsFn         := fun s => "parametric attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
};
let attrImpl : AttributeImpl := {
  name  := name,
  descr := descr,
  add   := fun env decl args persistent => do
    unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString name ++ "', must be persistent"));
    unless (env.getModuleIdxFor decl).isNone $
      throw (IO.userError ("invalid attribute '" ++ toString name ++ "', declaration is in an imported module"));
    match getParam env decl args with
    | Except.error msg => throw (IO.userError ("invalid attribute '" ++ toString name ++ "', " ++ msg))
    | Except.ok val    => do
      let env := ext.addEntry env (decl, val);
      match afterSet env decl val with
      | Except.error msg => throw (IO.userError ("invalid attribute '" ++ toString name ++ "', " ++ msg))
      | Except.ok env    => pure env
};
registerAttribute attrImpl;
pure { attr := attrImpl, ext := ext }

namespace ParametricAttribute

instance {α : Type} : Inhabited (ParametricAttribute α) := ⟨{attr := default _, ext := default _}⟩

def getParam {α : Type} [Inhabited α] (attr : ParametricAttribute α) (env : Environment) (decl : Name) : Option α :=
match env.getModuleIdxFor decl with
| some modIdx =>
  match (attr.ext.getModuleEntries env modIdx).binSearch (decl, default _) (fun a b => Name.quickLt a.1 b.1) with
  | some (_, val) => some val
  | none          => none
| none        => (attr.ext.getState env).find decl

def setParam {α : Type} (attr : ParametricAttribute α) (env : Environment) (decl : Name) (param : α) : Except String Environment :=
if (env.getModuleIdxFor decl).isSome then
  Except.error ("invalid '" ++ toString attr.attr.name ++ "'.setParam, declaration is in an imported module")
else if ((attr.ext.getState env).find decl).isSome then
  Except.error ("invalid '" ++ toString attr.attr.name ++ "'.setParam, attribute has already been set")
else
  Except.ok (attr.ext.addEntry env (decl, param))

end ParametricAttribute

/-
  Given a list `[a₁, ..., a_n]` of elements of type `α`, `EnumAttributes` provides an attribute `Attr_i` for
  associating a value `a_i` with an declaration. `α` is usually an enumeration type.
  Note that whenever we register an `EnumAttributes`, we create `n` attributes, but only one environment extension. -/
structure EnumAttributes (α : Type) :=
(attrs : List AttributeImpl)
(ext   : PersistentEnvExtension (Name × α) (NameMap α))

def registerEnumAttributes {α : Type} [Inhabited α] (extName : Name) (attrDescrs : List (Name × String × α)) (validate : Environment → Name → α → Except String Unit := fun _ _ _ => Except.ok ()) : IO (EnumAttributes α) :=
do
ext : PersistentEnvExtension (Name × α) (NameMap α) ← registerPersistentEnvExtension {
  name            := extName,
  addImportedFn   := fun _ => pure {},
  addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2,
  exportEntriesFn := fun m =>
    let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) Array.empty;
    r.qsort (fun a b => Name.quickLt a.1 b.1),
  statsFn         := fun s => "enumeration attribute extension" ++ Format.line ++ "number of local entries: " ++ format s.size
};
let attrs := attrDescrs.map $ fun ⟨name, descr, val⟩ => { AttributeImpl .
  name  := name,
  descr := descr,
  add   := fun env decl args persistent => do
    unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString name ++ "', must be persistent"));
    unless (env.getModuleIdxFor decl).isNone $
      throw (IO.userError ("invalid attribute '" ++ toString name ++ "', declaration is in an imported module"));
    match validate env decl val with
    | Except.error msg => throw (IO.userError ("invalid attribute '" ++ toString name ++ "', " ++ msg))
    | _                => pure $ ext.addEntry env (decl, val)
};
attrs.mfor registerAttribute;
pure { ext := ext, attrs := attrs }

namespace EnumAttributes

instance {α : Type} : Inhabited (EnumAttributes α) := ⟨{attrs := [], ext := default _}⟩

def getValue {α : Type} [Inhabited α] (attr : EnumAttributes α) (env : Environment) (decl : Name) : Option α :=
match env.getModuleIdxFor decl with
| some modIdx =>
  match (attr.ext.getModuleEntries env modIdx).binSearch (decl, default _) (fun a b => Name.quickLt a.1 b.1) with
  | some (_, val) => some val
  | none          => none
| none        => (attr.ext.getState env).find decl

def setValue {α : Type} (attrs : EnumAttributes α) (env : Environment) (decl : Name) (val : α) : Except String Environment :=
if (env.getModuleIdxFor decl).isSome then
  Except.error ("invalid '" ++ toString attrs.ext.name ++ "'.setValue, declaration is in an imported module")
else if ((attrs.ext.getState env).find decl).isSome then
  Except.error ("invalid '" ++ toString attrs.ext.name ++ "'.setValue, attribute has already been set")
else
  Except.ok (attrs.ext.addEntry env (decl, val))

end EnumAttributes

/- Helper function for converting a Syntax object representing attribute parameters into an identifier.
   It returns `none` if the parameter is not a simple identifier.

   Remark: in the future, attributes should define their own parsers, and we should use `match_syntax` to
   decode the Syntax object. -/
def attrParamSyntaxToIdentifier (s : Syntax) : Option Name :=
match s with
| Syntax.node k args =>
  if k == nullKind && args.size == 1 then match args.get! 0 with
    | Syntax.ident _ _ id _ => some id
    | _ => none
  else
    none
| _ => none

end Lean

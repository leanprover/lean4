/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Scopes
import Lean.Syntax
import Lean.CoreM

namespace Lean

inductive AttributeApplicationTime
| afterTypeChecking | afterCompilation | beforeElaboration

def AttributeApplicationTime.beq : AttributeApplicationTime → AttributeApplicationTime → Bool
| AttributeApplicationTime.afterTypeChecking, AttributeApplicationTime.afterTypeChecking => true
| AttributeApplicationTime.afterCompilation,  AttributeApplicationTime.afterCompilation  => true
| AttributeApplicationTime.beforeElaboration, AttributeApplicationTime.beforeElaboration => true
| _,                                          _                                          => false

instance AttributeApplicationTime.hasBeq : HasBeq AttributeApplicationTime := ⟨AttributeApplicationTime.beq⟩

-- TODO: after we delete the old frontend, we should use `EIO` with a richer exception kind at AttributeImpl.
-- We must perform a similar modification at `PersistentEnvExtension`

structure AttributeImpl :=
(name : Name)
(descr : String)
(add (decl : Name) (args : Syntax) (persistent : Bool) : CoreM Unit)
/-
(addScoped (env : Environment) (decl : Name) (args : Syntax) : IO Environment
           := throw (IO.userError ("attribute '" ++ toString name ++ "' does not support scopes")))
(erase (env : Environment) (decl : Name) (persistent : Bool) : IO Environment
       := throw (IO.userError ("attribute '" ++ toString name ++ "' does not support removal")))
(activateScoped (env : Environment) (scope : Name) : IO Environment := pure env)
(pushScope (env : Environment) : IO Environment := pure env)
(popScope (env : Environment) : IO Environment := pure env)
-/
(applicationTime := AttributeApplicationTime.afterTypeChecking)

instance AttributeImpl.inhabited : Inhabited AttributeImpl :=
⟨{ name := arbitrary _, descr := arbitrary _, add := fun env _ _ _ => pure () }⟩

open Std (PersistentHashMap)

def mkAttributeMapRef : IO (IO.Ref (PersistentHashMap Name AttributeImpl)) :=
IO.mkRef {}

@[init mkAttributeMapRef]
constant attributeMapRef : IO.Ref (PersistentHashMap Name AttributeImpl) := arbitrary _

/- Low level attribute registration function. -/
def registerBuiltinAttribute (attr : AttributeImpl) : IO Unit := do
m ← attributeMapRef.get;
when (m.contains attr.name) $ throw (IO.userError ("invalid builtin attribute declaration, '" ++ toString attr.name ++ "' has already been used"));
initializing ← IO.initializing;
unless initializing $ throw (IO.userError ("failed to register attribute, attributes can only be registered during initialization"));
attributeMapRef.modify (fun m => m.insert attr.name attr)

abbrev AttributeImplBuilder := List DataValue → Except String AttributeImpl
abbrev AttributeImplBuilderTable := Std.HashMap Name AttributeImplBuilder

def mkAttributeImplBuilderTable : IO (IO.Ref AttributeImplBuilderTable) := IO.mkRef {}
@[init mkAttributeImplBuilderTable] constant attributeImplBuilderTableRef : IO.Ref AttributeImplBuilderTable := arbitrary _

def registerAttributeImplBuilder (builderId : Name) (builder : AttributeImplBuilder) : IO Unit := do
table ← attributeImplBuilderTableRef.get;
when (table.contains builderId) $ throw (IO.userError ("attribute implementation builder '" ++ toString builderId ++ "' has already been declared"));
attributeImplBuilderTableRef.modify $ fun table => table.insert builderId builder

def mkAttributeImplOfBuilder (builderId : Name) (args : List DataValue) : IO AttributeImpl := do
table ← attributeImplBuilderTableRef.get;
match table.find? builderId with
| none         => throw (IO.userError ("unknown attribute implementation builder '" ++ toString builderId ++ "'"))
| some builder => IO.ofExcept $ builder args

inductive AttributeExtensionOLeanEntry
| decl (declName : Name) -- `declName` has type `AttributeImpl`
| builder (builderId : Name) (args : List DataValue)

structure AttributeExtensionState :=
(newEntries : List AttributeExtensionOLeanEntry := [])
(map        : PersistentHashMap Name AttributeImpl)

abbrev AttributeExtension := PersistentEnvExtension AttributeExtensionOLeanEntry (AttributeExtensionOLeanEntry × AttributeImpl) AttributeExtensionState

instance AttributeExtensionState.inhabited : Inhabited AttributeExtensionState := ⟨{ map := {} }⟩

private def AttributeExtension.mkInitial : IO AttributeExtensionState := do
map ← attributeMapRef.get;
pure { map := map }

unsafe def mkAttributeImplOfConstantUnsafe (env : Environment) (declName : Name) : Except String AttributeImpl :=
match env.find? declName with
| none      => throw ("unknow constant '" ++ toString declName ++ "'")
| some info =>
  match info.type with
  | Expr.const `Lean.AttributeImpl _ _ => env.evalConst AttributeImpl declName
  | _ => throw ("unexpected attribute implementation type at '" ++ toString declName ++ "' (`AttributeImpl` expected")

@[implementedBy mkAttributeImplOfConstantUnsafe]
constant mkAttributeImplOfConstant (env : Environment) (declName : Name) : Except String AttributeImpl := arbitrary _

def mkAttributeImplOfEntry (env : Environment) (e : AttributeExtensionOLeanEntry) : IO AttributeImpl :=
match e with
| AttributeExtensionOLeanEntry.decl declName          => IO.ofExcept $ mkAttributeImplOfConstant env declName
| AttributeExtensionOLeanEntry.builder builderId args => mkAttributeImplOfBuilder builderId args

private def AttributeExtension.addImported (env : Environment) (es : Array (Array AttributeExtensionOLeanEntry)) : IO AttributeExtensionState := do
map ← attributeMapRef.get;
map ← es.foldlM
  (fun map entries =>
    entries.foldlM
      (fun (map : PersistentHashMap Name AttributeImpl) entry => do
        attrImpl ← mkAttributeImplOfEntry env entry;
        pure $ map.insert attrImpl.name attrImpl)
      map)
  map;
pure { map := map }

private def AttributeExtension.addEntry (s : AttributeExtensionState) (e : AttributeExtensionOLeanEntry × AttributeImpl) : AttributeExtensionState :=
{ s with map := s.map.insert e.2.name e.2, newEntries := e.1 :: s.newEntries }

def mkAttributeExtension : IO AttributeExtension :=
registerPersistentEnvExtension {
  name            := `attrExt,
  mkInitial       := AttributeExtension.mkInitial,
  addImportedFn   := AttributeExtension.addImported,
  addEntryFn      := AttributeExtension.addEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
}

@[init mkAttributeExtension]
def attributeExtension : AttributeExtension := arbitrary _

/- Return true iff `n` is the name of a registered attribute. -/
@[export lean_is_attribute]
def isBuiltinAttribute (n : Name) : IO Bool := do
m ← attributeMapRef.get; pure (m.contains n)

/- Return the name of all registered attributes. -/
def getBuiltinAttributeNames : IO (List Name) := do
m ← attributeMapRef.get; pure $ m.foldl (fun r n _ => n::r) []

def getBuiltinAttributeImpl (attrName : Name) : IO AttributeImpl := do
m ← attributeMapRef.get;
match m.find? attrName with
| some attr => pure attr
| none      => throw (IO.userError ("unknown attribute '" ++ toString attrName ++ "'"))

@[export lean_attribute_application_time]
def getBuiltinAttributeApplicationTime (n : Name) : IO AttributeApplicationTime := do
attr ← getBuiltinAttributeImpl n;
pure attr.applicationTime

def isAttribute (env : Environment) (attrName : Name) : Bool :=
(attributeExtension.getState env).map.contains attrName

def getAttributeNames (env : Environment) : List Name :=
let m := (attributeExtension.getState env).map;
m.foldl (fun r n _ => n::r) []

def getAttributeImpl (env : Environment) (attrName : Name) : Except String AttributeImpl :=
let m := (attributeExtension.getState env).map;
match m.find? attrName with
| some attr => pure attr
| none      => throw ("unknown attribute '" ++ toString attrName ++ "'")

def registerAttributeOfDecl (env : Environment) (attrDeclName : Name) : Except String Environment := do
attrImpl ← mkAttributeImplOfConstant env attrDeclName;
if isAttribute env attrImpl.name then
  throw ("invalid builtin attribute declaration, '" ++ toString attrImpl.name ++ "' has already been used")
else
  pure $ attributeExtension.addEntry env (AttributeExtensionOLeanEntry.decl attrDeclName, attrImpl)

def registerAttributeOfBuilder (env : Environment) (builderId : Name) (args : List DataValue) : IO Environment := do
attrImpl ← mkAttributeImplOfBuilder builderId args;
if isAttribute env attrImpl.name then
  throw (IO.userError ("invalid builtin attribute declaration, '" ++ toString attrImpl.name ++ "' has already been used"))
else
  pure $ attributeExtension.addEntry env (AttributeExtensionOLeanEntry.builder builderId args, attrImpl)

namespace Environment

/- Add attribute `attr` to declaration `decl` with arguments `args`. If `persistent == true`, then attribute is saved on .olean file.
   It throws an error when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support `persistent == false`.
   - `args` is not valid for `attr`. -/
@[export lean_add_attribute]
def addAttribute (env : Environment) (decl : Name) (attrName : Name) (args : Syntax := Syntax.missing) (persistent := true) : IO Environment := do
attr ← IO.ofExcept $ getAttributeImpl env attrName;
(env, _) ← (attr.add decl args persistent).run' env;
pure env

/-
/- Add a scoped attribute `attr` to declaration `decl` with arguments `args` and scope `decl.getPrefix`.
   Scoped attributes are always persistent.
   It returns `Except.error` when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support scoped attributes.
   - `args` is not valid for `attr`.

   Remark: the attribute will not be activated if `decl` is not inside the current namespace `env.getNamespace`. -/
@[export lean_add_scoped_attribute]
def addScopedAttribute (env : Environment) (decl : Name) (attrName : Name) (args : Syntax := Syntax.missing) : IO Environment := do
attr ← getAttributeImpl attrName;
attr.addScoped env decl args

/- Remove attribute `attr` from declaration `decl`. The effect is the current scope.
   It returns `Except.error` when
   - `attr` is not the name of an attribute registered in the system.
   - `attr` does not support erasure.
   - `args` is not valid for `attr`. -/
@[export lean_erase_attribute]
def eraseAttribute (env : Environment) (decl : Name) (attrName : Name) (persistent := true) : IO Environment := do
attr ← getAttributeImpl attrName;
attr.erase env decl persistent

/- Activate the scoped attribute `attr` for all declarations in scope `scope`.
   We use this function to implement the command `open foo`. -/
@[export lean_activate_scoped_attribute]
def activateScopedAttribute (env : Environment) (attrName : Name) (scope : Name) : IO Environment := do
attr ← getAttributeImpl attrName;
attr.activateScoped env scope

/- Activate all scoped attributes at `scope` -/
@[export lean_activate_scoped_attributes]
def activateScopedAttributes (env : Environment) (scope : Name) : IO Environment := do
attrs ← attributeArrayRef.get;
attrs.foldlM (fun env attr => attr.activateScoped env scope) env
-/

/- We use this function to implement commands `namespace foo` and `section foo`.
   It activates scoped attributes in the new resulting namespace. -/
@[export lean_push_scope]
def pushScope (env : Environment) (header : Name) (isNamespace : Bool) : IO Environment := do
let env := env.pushScopeCore header isNamespace;
let ns  := env.getNamespace;
-- attrs ← attributeArrayRef.get;
-- attrs.foldlM (fun env attr => do env ← attr.pushScope env; if isNamespace then attr.activateScoped env ns else pure env) env
pure env

/- We use this function to implement commands `end foo` for closing namespaces and sections. -/
@[export lean_pop_scope]
def popScope (env : Environment) : IO Environment := do
let env := env.popScopeCore;
-- attrs ← attributeArrayRef.get;
-- attrs.foldlM (fun env attr => attr.popScope env) env
pure env

end Environment

/--
  Tag attributes are simple and efficient. They are useful for marking declarations in the modules where
  they were defined.

  The startup cost for this kind of attribute is very small since `addImportedFn` is a constant function.

  They provide the predicate `tagAttr.hasTag env decl` which returns true iff declaration `decl`
  is tagged in the environment `env`. -/
structure TagAttribute :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension Name Name NameSet)

def registerTagAttribute (name : Name) (descr : String) (validate : Name → CoreM Unit := fun _ => pure ()) : IO TagAttribute := do
ext : PersistentEnvExtension Name Name NameSet ← registerPersistentEnvExtension {
  name            := name,
  mkInitial       := pure {},
  addImportedFn   := fun _ _ => pure {},
  addEntryFn      := fun (s : NameSet) n => s.insert n,
  exportEntriesFn := fun es =>
    let r : Array Name := es.fold (fun a e => a.push e) #[];
    r.qsort Name.quickLt,
  statsFn         := fun s => "tag attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
};
let attrImpl : AttributeImpl := {
  name  := name,
  descr := descr,
  add   := fun decl args persistent => do
    when args.hasArgs $ Core.throwError ("invalid attribute '" ++ toString name ++ "', unexpected argument");
    unless persistent $ Core.throwError ("invalid attribute '" ++ toString name ++ "', must be persistent");
    env ← Core.getEnv;
    unless (env.getModuleIdxFor? decl).isNone $
      Core.throwError ("invalid attribute '" ++ toString name ++ "', declaration is in an imported module");
    validate decl;
    Core.setEnv $ ext.addEntry env decl
};
registerBuiltinAttribute attrImpl;
pure { attr := attrImpl, ext := ext }

namespace TagAttribute

instance : Inhabited TagAttribute := ⟨{attr := arbitrary _, ext := arbitrary _}⟩

def hasTag (attr : TagAttribute) (env : Environment) (decl : Name) : Bool :=
match env.getModuleIdxFor? decl with
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
(ext  : PersistentEnvExtension (Name × α) (Name × α) (NameMap α))

def registerParametricAttribute {α : Type} [Inhabited α] (name : Name) (descr : String)
    (getParam : Name → Syntax → CoreM α)
    (afterSet : Name → α → CoreM Unit := fun env _ _ => pure ())
    (appTime := AttributeApplicationTime.afterTypeChecking)
    : IO (ParametricAttribute α) := do
ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
  name            := name,
  mkInitial       := pure {},
  addImportedFn   := fun _ _ => pure {},
  addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2,
  exportEntriesFn := fun m =>
    let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[];
    r.qsort (fun a b => Name.quickLt a.1 b.1),
  statsFn         := fun s => "parametric attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
};
let attrImpl : AttributeImpl := {
  name  := name,
  descr := descr,
  applicationTime := appTime,
  add   := fun decl args persistent => do
    unless persistent $ Core.throwError ("invalid attribute '" ++ toString name ++ "', must be persistent");
    env ← Core.getEnv;
    unless (env.getModuleIdxFor? decl).isNone $
      Core.throwError ("invalid attribute '" ++ toString name ++ "', declaration is in an imported module");
    val ← getParam decl args;
    let env' := ext.addEntry env (decl, val);
    Core.setEnv env';
    catch (afterSet decl val) (fun _ => Core.setEnv env)
};
registerBuiltinAttribute attrImpl;
pure { attr := attrImpl, ext := ext }

namespace ParametricAttribute

instance {α : Type} : Inhabited (ParametricAttribute α) := ⟨{attr := arbitrary _, ext := arbitrary _}⟩

def getParam {α : Type} [Inhabited α] (attr : ParametricAttribute α) (env : Environment) (decl : Name) : Option α :=
match env.getModuleIdxFor? decl with
| some modIdx =>
  match (attr.ext.getModuleEntries env modIdx).binSearch (decl, arbitrary _) (fun a b => Name.quickLt a.1 b.1) with
  | some (_, val) => some val
  | none          => none
| none        => (attr.ext.getState env).find? decl

def setParam {α : Type} (attr : ParametricAttribute α) (env : Environment) (decl : Name) (param : α) : Except String Environment :=
if (env.getModuleIdxFor? decl).isSome then
  Except.error ("invalid '" ++ toString attr.attr.name ++ "'.setParam, declaration is in an imported module")
else if ((attr.ext.getState env).find? decl).isSome then
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
(ext   : PersistentEnvExtension (Name × α) (Name × α) (NameMap α))

def registerEnumAttributes {α : Type} [Inhabited α] (extName : Name) (attrDescrs : List (Name × String × α))
    (validate : Name → α → CoreM Unit := fun _ _ => pure ())
    (applicationTime := AttributeApplicationTime.afterTypeChecking) : IO (EnumAttributes α) := do
ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
  name            := extName,
  mkInitial       := pure {},
  addImportedFn   := fun _ _ => pure {},
  addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2,
  exportEntriesFn := fun m =>
    let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[];
    r.qsort (fun a b => Name.quickLt a.1 b.1),
  statsFn         := fun s => "enumeration attribute extension" ++ Format.line ++ "number of local entries: " ++ format s.size
};
let attrs := attrDescrs.map $ fun ⟨name, descr, val⟩ => {
  name            := name,
  descr           := descr,
  applicationTime := applicationTime,
  add             := (fun decl args persistent => do
    unless persistent $ Core.throwError ("invalid attribute '" ++ toString name ++ "', must be persistent");
    env ← Core.getEnv;
    unless (env.getModuleIdxFor? decl).isNone $
      Core.throwError ("invalid attribute '" ++ toString name ++ "', declaration is in an imported module");
    validate decl val;
    Core.setEnv $ ext.addEntry env (decl, val))
  : AttributeImpl
};
attrs.forM registerBuiltinAttribute;
pure { ext := ext, attrs := attrs }

namespace EnumAttributes

instance {α : Type} : Inhabited (EnumAttributes α) := ⟨{attrs := [], ext := arbitrary _}⟩

def getValue {α : Type} [Inhabited α] (attr : EnumAttributes α) (env : Environment) (decl : Name) : Option α :=
match env.getModuleIdxFor? decl with
| some modIdx =>
  match (attr.ext.getModuleEntries env modIdx).binSearch (decl, arbitrary _) (fun a b => Name.quickLt a.1 b.1) with
  | some (_, val) => some val
  | none          => none
| none        => (attr.ext.getState env).find? decl

def setValue {α : Type} (attrs : EnumAttributes α) (env : Environment) (decl : Name) (val : α) : Except String Environment :=
if (env.getModuleIdxFor? decl).isSome then
  Except.error ("invalid '" ++ toString attrs.ext.name ++ "'.setValue, declaration is in an imported module")
else if ((attrs.ext.getState env).find? decl).isSome then
  Except.error ("invalid '" ++ toString attrs.ext.name ++ "'.setValue, attribute has already been set")
else
  Except.ok (attrs.ext.addEntry env (decl, val))

end EnumAttributes

/--
  Helper function for converting a Syntax object representing attribute parameters into an identifier.
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

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Syntax
import Lean.CoreM
import Lean.ResolveName

namespace Lean

inductive AttributeApplicationTime
  | afterTypeChecking | afterCompilation | beforeElaboration

def AttributeApplicationTime.beq : AttributeApplicationTime → AttributeApplicationTime → Bool
  | AttributeApplicationTime.afterTypeChecking, AttributeApplicationTime.afterTypeChecking => true
  | AttributeApplicationTime.afterCompilation,  AttributeApplicationTime.afterCompilation  => true
  | AttributeApplicationTime.beforeElaboration, AttributeApplicationTime.beforeElaboration => true
  | _,                                          _                                          => false

instance : BEq AttributeApplicationTime := ⟨AttributeApplicationTime.beq⟩

structure Attr.Context :=
  (currNamespace : Name)
  (openDecls     : List OpenDecl)

abbrev AttrM := ReaderT Attr.Context CoreM

instance : MonadLift ImportM AttrM := {
  monadLift := fun x => do liftM (m := IO) (x { env := (← getEnv), opts := (← getOptions) })
}

instance : MonadResolveName AttrM := {
  getCurrNamespace := do pure (← read).currNamespace,
  getOpenDecls     := do pure (← read).openDecls
}

structure AttributeImplCore :=
  (name : Name)
  (descr : String)
  (applicationTime := AttributeApplicationTime.afterTypeChecking)

structure AttributeImpl extends AttributeImplCore :=
  (add (decl : Name) (args : Syntax) (persistent : Bool) : AttrM Unit)

instance : Inhabited AttributeImpl :=
  ⟨{ name := arbitrary _, descr := arbitrary _, add := fun env _ _ _ => pure () }⟩

open Std (PersistentHashMap)

builtin_initialize attributeMapRef : IO.Ref (PersistentHashMap Name AttributeImpl) ← IO.mkRef {}

/- Low level attribute registration function. -/
def registerBuiltinAttribute (attr : AttributeImpl) : IO Unit := do
  let m ← attributeMapRef.get
  if m.contains attr.name then throw (IO.userError ("invalid builtin attribute declaration, '" ++ toString attr.name ++ "' has already been used"))
  unless (← IO.initializing) do throw (IO.userError "failed to register attribute, attributes can only be registered during initialization")
  attributeMapRef.modify fun m => m.insert attr.name attr

abbrev AttributeImplBuilder := List DataValue → Except String AttributeImpl
abbrev AttributeImplBuilderTable := Std.HashMap Name AttributeImplBuilder

builtin_initialize attributeImplBuilderTableRef : IO.Ref AttributeImplBuilderTable ← IO.mkRef {}

def registerAttributeImplBuilder (builderId : Name) (builder : AttributeImplBuilder) : IO Unit := do
  let table ← attributeImplBuilderTableRef.get
  if table.contains builderId then throw (IO.userError ("attribute implementation builder '" ++ toString builderId ++ "' has already been declared"))
  attributeImplBuilderTableRef.modify fun table => table.insert builderId builder

def mkAttributeImplOfBuilder (builderId : Name) (args : List DataValue) : IO AttributeImpl := do
  let table ← attributeImplBuilderTableRef.get
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

instance : Inhabited AttributeExtensionState := ⟨{ map := {} }⟩

private def AttributeExtension.mkInitial : IO AttributeExtensionState := do
  let map ← attributeMapRef.get
  pure { map := map }

unsafe def mkAttributeImplOfConstantUnsafe (env : Environment) (opts : Options) (declName : Name) : Except String AttributeImpl :=
  match env.find? declName with
  | none      => throw ("unknow constant '" ++ toString declName ++ "'")
  | some info =>
    match info.type with
    | Expr.const `Lean.AttributeImpl _ _ => env.evalConst AttributeImpl opts declName
    | _ => throw ("unexpected attribute implementation type at '" ++ toString declName ++ "' (`AttributeImpl` expected")

@[implementedBy mkAttributeImplOfConstantUnsafe]
constant mkAttributeImplOfConstant (env : Environment) (opts : Options) (declName : Name) : Except String AttributeImpl

def mkAttributeImplOfEntry (env : Environment) (opts : Options) (e : AttributeExtensionOLeanEntry) : IO AttributeImpl :=
  match e with
  | AttributeExtensionOLeanEntry.decl declName          => IO.ofExcept $ mkAttributeImplOfConstant env opts declName
  | AttributeExtensionOLeanEntry.builder builderId args => mkAttributeImplOfBuilder builderId args

private def AttributeExtension.addImported (es : Array (Array AttributeExtensionOLeanEntry)) : ImportM AttributeExtensionState := do
  let ctx ← read
  let map ← attributeMapRef.get
  let map ← es.foldlM
    (fun map entries =>
      entries.foldlM
        (fun (map : PersistentHashMap Name AttributeImpl) entry => do
          let attrImpl ← liftM $ mkAttributeImplOfEntry ctx.env ctx.opts entry
          pure $ map.insert attrImpl.name attrImpl)
        map)
    map
  pure { map := map }

private def addAttrEntry (s : AttributeExtensionState) (e : AttributeExtensionOLeanEntry × AttributeImpl) : AttributeExtensionState :=
  { s with map := s.map.insert e.2.name e.2, newEntries := e.1 :: s.newEntries }

builtin_initialize attributeExtension : AttributeExtension ←
  registerPersistentEnvExtension {
    name            := `attrExt,
    mkInitial       := AttributeExtension.mkInitial,
    addImportedFn   := AttributeExtension.addImported,
    addEntryFn      := addAttrEntry,
    exportEntriesFn := fun s => s.newEntries.reverse.toArray,
    statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
  }

/- Return true iff `n` is the name of a registered attribute. -/
@[export lean_is_attribute]
def isBuiltinAttribute (n : Name) : IO Bool := do
  let m ← attributeMapRef.get; pure (m.contains n)

/- Return the name of all registered attributes. -/
def getBuiltinAttributeNames : IO (List Name) := do
  let m ← attributeMapRef.get; pure $ m.foldl (fun r n _ => n::r) []

def getBuiltinAttributeImpl (attrName : Name) : IO AttributeImpl := do
  let m ← attributeMapRef.get
  match m.find? attrName with
  | some attr => pure attr
  | none      => throw (IO.userError ("unknown attribute '" ++ toString attrName ++ "'"))

@[export lean_attribute_application_time]
def getBuiltinAttributeApplicationTime (n : Name) : IO AttributeApplicationTime := do
  let attr ← getBuiltinAttributeImpl n
  pure attr.applicationTime

def isAttribute (env : Environment) (attrName : Name) : Bool :=
  (attributeExtension.getState env).map.contains attrName

def getAttributeNames (env : Environment) : List Name :=
  let m := (attributeExtension.getState env).map
  m.foldl (fun r n _ => n::r) []

def getAttributeImpl (env : Environment) (attrName : Name) : Except String AttributeImpl :=
  let m := (attributeExtension.getState env).map
  match m.find? attrName with
  | some attr => pure attr
  | none      => throw ("unknown attribute '" ++ toString attrName ++ "'")

def registerAttributeOfDecl (env : Environment) (opts : Options) (attrDeclName : Name) : Except String Environment := do
  let attrImpl ← mkAttributeImplOfConstant env opts attrDeclName
  if isAttribute env attrImpl.name then
    throw ("invalid builtin attribute declaration, '" ++ toString attrImpl.name ++ "' has already been used")
  else
    pure $ attributeExtension.addEntry env (AttributeExtensionOLeanEntry.decl attrDeclName, attrImpl)

def registerAttributeOfBuilder (env : Environment) (builderId : Name) (args : List DataValue) : IO Environment := do
  let attrImpl ← mkAttributeImplOfBuilder builderId args
  if isAttribute env attrImpl.name then
    throw (IO.userError ("invalid builtin attribute declaration, '" ++ toString attrImpl.name ++ "' has already been used"))
  else
    pure $ attributeExtension.addEntry env (AttributeExtensionOLeanEntry.builder builderId args, attrImpl)

def addAttribute (decl : Name) (attrName : Name) (args : Syntax) (persistent : Bool := true) : AttrM Unit := do
  let env ← getEnv
  let attr ← ofExcept $ getAttributeImpl env attrName
  attr.add decl args persistent

/--
  Tag attributes are simple and efficient. They are useful for marking declarations in the modules where
  they were defined.

  The startup cost for this kind of attribute is very small since `addImportedFn` is a constant function.

  They provide the predicate `tagAttr.hasTag env decl` which returns true iff declaration `decl`
  is tagged in the environment `env`. -/
structure TagAttribute :=
  (attr : AttributeImpl)
  (ext  : PersistentEnvExtension Name Name NameSet)

def registerTagAttribute (name : Name) (descr : String) (validate : Name → AttrM Unit := fun _ => pure ()) : IO TagAttribute := do
  let ext : PersistentEnvExtension Name Name NameSet ← registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure {},
    addImportedFn   := fun _ _ => pure {},
    addEntryFn      := fun (s : NameSet) n => s.insert n,
    exportEntriesFn := fun es =>
      let r : Array Name := es.fold (fun a e => a.push e) #[]
      r.qsort Name.quickLt,
    statsFn         := fun s => "tag attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrImpl : AttributeImpl := {
    name  := name,
    descr := descr,
    add   := fun decl args persistent => do
      if args.hasArgs then throwError! "invalid attribute '{name}', unexpected argument"
      unless persistent do throwError! "invalid attribute '{name}', must be persistent"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError! "invalid attribute '{name}', declaration is in an imported module"
      validate decl
      let env ← getEnv
      setEnv $ ext.addEntry env decl
  }
  registerBuiltinAttribute attrImpl
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

structure ParametricAttributeImpl (α : Type) extends AttributeImplCore :=
  (getParam : Name → Syntax → AttrM α)
  (afterSet : Name → α → AttrM Unit := fun env _ _ => pure ())
  (afterImport : Array (Array (Name × α)) → ImportM Unit := fun _ => pure ())

def registerParametricAttribute {α : Type} [Inhabited α] (impl : ParametricAttributeImpl α) : IO (ParametricAttribute α) := do
  let ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
    name            := impl.name,
    mkInitial       := pure {},
    addImportedFn   := fun s => impl.afterImport s *> pure {},
    addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2,
    exportEntriesFn := fun m =>
      let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1),
    statsFn         := fun s => "parametric attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrImpl : AttributeImpl := { impl with
    add   := fun decl args persistent => do
      unless persistent do throwError! "invalid attribute '{impl.name}', must be persistent"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError! "invalid attribute '{impl.name}', declaration is in an imported module"
      let val ← impl.getParam decl args
      let env' := ext.addEntry env (decl, val)
      setEnv env'
      try impl.afterSet decl val catch _ => setEnv env
  }
  registerBuiltinAttribute attrImpl
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
    (validate : Name → α → AttrM Unit := fun _ _ => pure ())
    (applicationTime := AttributeApplicationTime.afterTypeChecking) : IO (EnumAttributes α) := do
  let ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
    name            := extName,
    mkInitial       := pure {},
    addImportedFn   := fun _ _ => pure {},
    addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2,
    exportEntriesFn := fun m =>
      let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1),
    statsFn         := fun s => "enumeration attribute extension" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrs := attrDescrs.map fun (name, descr, val) => {
    name            := name,
    descr           := descr,
    add             := fun decl args persistent => do
      unless persistent do throwError! "invalid attribute '{name}', must be persistent"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError! "invalid attribute '{name}', declaration is in an imported module"
      validate decl val
      setEnv $ ext.addEntry env (decl, val),
    applicationTime := applicationTime
    : AttributeImpl
  }
  attrs.forM registerBuiltinAttribute
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

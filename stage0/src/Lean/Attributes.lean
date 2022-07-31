/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Syntax
import Lean.CoreM
import Lean.ResolveName

namespace Lean

inductive AttributeApplicationTime where
  | afterTypeChecking | afterCompilation | beforeElaboration
  deriving Inhabited, BEq

abbrev AttrM := CoreM

instance : MonadLift ImportM AttrM where
  monadLift x := do liftM (m := IO) (x { env := (← getEnv), opts := (← getOptions) })

structure AttributeImplCore where
  /-- This is used as the target for go-to-definition queries for simple attributes -/
  ref : Name := by exact decl_name%
  name : Name
  descr : String
  applicationTime := AttributeApplicationTime.afterTypeChecking
  deriving Inhabited

/-- You can tag attributes with the 'local' or 'scoped' kind.
For example: `attribute [local myattr, scoped yourattr, theirattr]`.

This is used to indicate how an attribute should be scoped.
- local means that the attribute should only be applied in the current scope and forgotten once the current section, namespace, or file is closed.
- scoped means that the attribute should only be applied while the namespace is open.
- global means that the attribute should always be applied.

Note that the attribute handler (`AttributeImpl.add`) is responsible for interpreting the kind and
making sure that these kinds are respected.
-/
inductive AttributeKind
  | global | «local» | «scoped»
  deriving BEq, Inhabited

instance : ToString AttributeKind where
  toString
    | .global => "global"
    | .local  => "local"
    | .scoped => "scoped"

structure AttributeImpl extends AttributeImplCore where
  /-- This is run when the attribute is applied to a declaration `decl`. `stx` is the syntax of the attribute including arguments. -/
  add (decl : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Unit
  erase (decl : Name) : AttrM Unit := throwError "attribute cannot be erased"
  deriving Inhabited

open Std (PersistentHashMap)

builtin_initialize attributeMapRef : IO.Ref (PersistentHashMap Name AttributeImpl) ← IO.mkRef {}

/-- Low level attribute registration function. -/
def registerBuiltinAttribute (attr : AttributeImpl) : IO Unit := do
  let m ← attributeMapRef.get
  if m.contains attr.name then throw (IO.userError ("invalid builtin attribute declaration, '" ++ toString attr.name ++ "' has already been used"))
  unless (← initializing) do
    throw (IO.userError "failed to register attribute, attributes can only be registered during initialization")
  attributeMapRef.modify fun m => m.insert attr.name attr

/-!
  Helper methods for decoding the parameters of builtin attributes that are defined before `Lean.Parser`.
  We have the following ones:
  ```
  @[builtinAttrParser] def simple     := leading_parser ident >> optional ident >> optional priorityParser
  /- We can't use `simple` for `class`, `instance`, `export` and `macro` because they are  keywords. -/
  @[builtinAttrParser] def «class»    := leading_parser "class"
  @[builtinAttrParser] def «instance» := leading_parser "instance" >> optional priorityParser
  @[builtinAttrParser] def «macro»    := leading_parser "macro " >> ident
  ```
  Note that we need the parsers for `class`, `instance`, and `macros` because they are keywords.
-/

def Attribute.Builtin.ensureNoArgs (stx : Syntax) : AttrM Unit := do
  if stx.getKind == `Lean.Parser.Attr.simple && stx[1].isNone && stx[2].isNone then
    return ()
  else if stx.getKind == `Lean.Parser.Attr.«class» then
    return ()
  else match stx with
    | Syntax.missing => return () -- In the elaborator, we use `Syntax.missing` when creating attribute views for simple attributes such as `class and `inline
    | _              => throwErrorAt stx "unexpected attribute argument"

def Attribute.Builtin.getIdent? (stx : Syntax) : AttrM (Option Syntax) := do
  if stx.getKind == `Lean.Parser.Attr.simple then
    if !stx[1].isNone && stx[1][0].isIdent then
      return some stx[1][0]
    else
      return none
  /- We handle `macro` here because it is handled by the generic `KeyedDeclsAttribute -/
  else if stx.getKind == `Lean.Parser.Attr.«macro» || stx.getKind == `Lean.Parser.Attr.«export» then
    return some stx[1]
  else
    throwErrorAt stx "unexpected attribute argument"

def Attribute.Builtin.getIdent (stx : Syntax) : AttrM Syntax := do
  match (← getIdent? stx) with
  | some id => return id
  | none    => throwErrorAt stx "unexpected attribute argument, identifier expected"

def Attribute.Builtin.getId? (stx : Syntax) : AttrM (Option Name) := do
  let ident? ← getIdent? stx
  return Syntax.getId <$> ident?

def Attribute.Builtin.getId (stx : Syntax) : AttrM Name := do
  return (← getIdent stx).getId

def getAttrParamOptPrio (optPrioStx : Syntax) : AttrM Nat :=
  if optPrioStx.isNone then
    return eval_prio default
  else match optPrioStx[0].isNatLit? with
    | some prio => return prio
    | none => throwErrorAt optPrioStx "priority expected"

def Attribute.Builtin.getPrio (stx : Syntax) : AttrM Nat := do
  if stx.getKind == `Lean.Parser.Attr.simple then
    getAttrParamOptPrio stx[1]
  else
    throwErrorAt stx "unexpected attribute argument, optional priority expected"


/--
  Tag attributes are simple and efficient. They are useful for marking declarations in the modules where
  they were defined.

  The startup cost for this kind of attribute is very small since `addImportedFn` is a constant function.

  They provide the predicate `tagAttr.hasTag env decl` which returns true iff declaration `decl`
  is tagged in the environment `env`. -/
structure TagAttribute where
  attr : AttributeImpl
  ext  : PersistentEnvExtension Name Name NameSet
  deriving Inhabited

def registerTagAttribute (name : Name) (descr : String)
    (validate : Name → AttrM Unit := fun _ => pure ()) (ref : Name := by exact decl_name%) : IO TagAttribute := do
  let ext : PersistentEnvExtension Name Name NameSet ← registerPersistentEnvExtension {
    name            := name
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun (s : NameSet) n => s.insert n
    exportEntriesFn := fun es =>
      let r : Array Name := es.fold (fun a e => a.push e) #[]
      r.qsort Name.quickLt
    statsFn         := fun s => "tag attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrImpl : AttributeImpl := {
    ref   := ref
    name  := name
    descr := descr
    add   := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError "invalid attribute '{name}', declaration is in an imported module"
      validate decl
      let env ← getEnv
      setEnv <| ext.addEntry env decl
  }
  registerBuiltinAttribute attrImpl
  return { attr := attrImpl, ext := ext }

namespace TagAttribute

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
structure ParametricAttribute (α : Type) where
  attr : AttributeImpl
  ext  : PersistentEnvExtension (Name × α) (Name × α) (NameMap α)
  deriving Inhabited

structure ParametricAttributeImpl (α : Type) extends AttributeImplCore where
  /-- This is used as the target for go-to-definition queries for simple attributes -/
  getParam : Name → Syntax → AttrM α
  afterSet : Name → α → AttrM Unit := fun _ _ _ => pure ()
  afterImport : Array (Array (Name × α)) → ImportM Unit := fun _ => pure ()

def registerParametricAttribute {α : Type} [Inhabited α] (impl : ParametricAttributeImpl α) : IO (ParametricAttribute α) := do
  let ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
    name            := impl.name
    mkInitial       := pure {}
    addImportedFn   := fun s => impl.afterImport s *> pure {}
    addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s => "parametric attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrImpl : AttributeImpl := {
    ref   := impl.ref
    name  := impl.name
    descr := impl.descr
    add   := fun decl stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute '{impl.name}', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError "invalid attribute '{impl.name}', declaration is in an imported module"
      let val ← impl.getParam decl stx
      let env' := ext.addEntry env (decl, val)
      setEnv env'
      try impl.afterSet decl val catch _ => setEnv env
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

namespace ParametricAttribute

def getParam? {α : Type} [Inhabited α] (attr : ParametricAttribute α) (env : Environment) (decl : Name) : Option α :=
  match env.getModuleIdxFor? decl with
  | some modIdx =>
    match (attr.ext.getModuleEntries env modIdx).binSearch (decl, default) (fun a b => Name.quickLt a.1 b.1) with
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

/--
  Given a list `[a₁, ..., a_n]` of elements of type `α`, `EnumAttributes` provides an attribute `Attr_i` for
  associating a value `a_i` with an declaration. `α` is usually an enumeration type.
  Note that whenever we register an `EnumAttributes`, we create `n` attributes, but only one environment extension. -/
structure EnumAttributes (α : Type) where
  attrs : List AttributeImpl
  ext   : PersistentEnvExtension (Name × α) (Name × α) (NameMap α)
  deriving Inhabited

def registerEnumAttributes {α : Type} [Inhabited α] (extName : Name) (attrDescrs : List (Name × String × α))
    (validate : Name → α → AttrM Unit := fun _ _ => pure ())
    (applicationTime := AttributeApplicationTime.afterTypeChecking)
    (ref : Name := by exact decl_name%) : IO (EnumAttributes α) := do
  let ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
    name            := extName
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s => "enumeration attribute extension" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrs := attrDescrs.map fun (name, descr, val) => {
    ref             := ref
    name            := name
    descr           := descr
    add             := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError "invalid attribute '{name}', declaration is in an imported module"
      validate decl val
      setEnv <| ext.addEntry env (decl, val)
    applicationTime := applicationTime
    : AttributeImpl
  }
  attrs.forM registerBuiltinAttribute
  pure { ext := ext, attrs := attrs }

namespace EnumAttributes

def getValue {α : Type} [Inhabited α] (attr : EnumAttributes α) (env : Environment) (decl : Name) : Option α :=
  match env.getModuleIdxFor? decl with
  | some modIdx =>
    match (attr.ext.getModuleEntries env modIdx).binSearch (decl, default) (fun a b => Name.quickLt a.1 b.1) with
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

/-!
  Attribute extension and builders. We use builders to implement attribute factories for parser categories.
-/

abbrev AttributeImplBuilder := Name → List DataValue → Except String AttributeImpl
abbrev AttributeImplBuilderTable := Std.HashMap Name AttributeImplBuilder

builtin_initialize attributeImplBuilderTableRef : IO.Ref AttributeImplBuilderTable ← IO.mkRef {}

def registerAttributeImplBuilder (builderId : Name) (builder : AttributeImplBuilder) : IO Unit := do
  let table ← attributeImplBuilderTableRef.get
  if table.contains builderId then throw (IO.userError ("attribute implementation builder '" ++ toString builderId ++ "' has already been declared"))
  attributeImplBuilderTableRef.modify fun table => table.insert builderId builder

def mkAttributeImplOfBuilder (builderId ref : Name) (args : List DataValue) : IO AttributeImpl := do
  let table ← attributeImplBuilderTableRef.get
  match table.find? builderId with
  | none         => throw (IO.userError ("unknown attribute implementation builder '" ++ toString builderId ++ "'"))
  | some builder => IO.ofExcept <| builder ref args

inductive AttributeExtensionOLeanEntry where
  | decl (declName : Name) -- `declName` has type `AttributeImpl`
  | builder (builderId ref : Name) (args : List DataValue)

structure AttributeExtensionState where
  newEntries : List AttributeExtensionOLeanEntry := []
  map        : PersistentHashMap Name AttributeImpl
  deriving Inhabited

abbrev AttributeExtension := PersistentEnvExtension AttributeExtensionOLeanEntry (AttributeExtensionOLeanEntry × AttributeImpl) AttributeExtensionState

private def AttributeExtension.mkInitial : IO AttributeExtensionState := do
  let map ← attributeMapRef.get
  pure { map := map }

unsafe def mkAttributeImplOfConstantUnsafe (env : Environment) (opts : Options) (declName : Name) : Except String AttributeImpl :=
  match env.find? declName with
  | none      => throw ("unknow constant '" ++ toString declName ++ "'")
  | some info =>
    match info.type with
    | Expr.const `Lean.AttributeImpl _ => env.evalConst AttributeImpl opts declName
    | _ => throw ("unexpected attribute implementation type at '" ++ toString declName ++ "' (`AttributeImpl` expected")

@[implementedBy mkAttributeImplOfConstantUnsafe]
opaque mkAttributeImplOfConstant (env : Environment) (opts : Options) (declName : Name) : Except String AttributeImpl

def mkAttributeImplOfEntry (env : Environment) (opts : Options) (e : AttributeExtensionOLeanEntry) : IO AttributeImpl :=
  match e with
  | .decl declName              => IO.ofExcept <| mkAttributeImplOfConstant env opts declName
  | .builder builderId ref args => mkAttributeImplOfBuilder builderId ref args

private def AttributeExtension.addImported (es : Array (Array AttributeExtensionOLeanEntry)) : ImportM AttributeExtensionState := do
  let ctx ← read
  let map ← attributeMapRef.get
  let map ← es.foldlM
    (fun map entries =>
      entries.foldlM
        (fun (map : PersistentHashMap Name AttributeImpl) entry => do
          let attrImpl ← mkAttributeImplOfEntry ctx.env ctx.opts entry
          return map.insert attrImpl.name attrImpl)
        map)
    map
  pure { map := map }

private def addAttrEntry (s : AttributeExtensionState) (e : AttributeExtensionOLeanEntry × AttributeImpl) : AttributeExtensionState :=
  { s with map := s.map.insert e.2.name e.2, newEntries := e.1 :: s.newEntries }

builtin_initialize attributeExtension : AttributeExtension ←
  registerPersistentEnvExtension {
    name            := `attrExt
    mkInitial       := AttributeExtension.mkInitial
    addImportedFn   := AttributeExtension.addImported
    addEntryFn      := addAttrEntry
    exportEntriesFn := fun s => s.newEntries.reverse.toArray
    statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
  }

/-- Return true iff `n` is the name of a registered attribute. -/
@[export lean_is_attribute]
def isBuiltinAttribute (n : Name) : IO Bool := do
  let m ← attributeMapRef.get; pure (m.contains n)

/-- Return the name of all registered attributes. -/
def getBuiltinAttributeNames : IO (List Name) :=
  return (← attributeMapRef.get).foldl (init := []) fun r n _ => n::r

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
    return attributeExtension.addEntry env (.decl attrDeclName, attrImpl)

def registerAttributeOfBuilder (env : Environment) (builderId ref : Name) (args : List DataValue) : IO Environment := do
  let attrImpl ← mkAttributeImplOfBuilder builderId ref args
  if isAttribute env attrImpl.name then
    throw (IO.userError ("invalid builtin attribute declaration, '" ++ toString attrImpl.name ++ "' has already been used"))
  else
    return attributeExtension.addEntry env (.builder builderId ref args, attrImpl)

def Attribute.add (declName : Name) (attrName : Name) (stx : Syntax) (kind := AttributeKind.global) : AttrM Unit := do
  let attr ← ofExcept <| getAttributeImpl (← getEnv) attrName
  attr.add declName stx kind

def Attribute.erase (declName : Name) (attrName : Name) : AttrM Unit := do
  let attr ← ofExcept <| getAttributeImpl (← getEnv) attrName
  attr.erase declName

/-- `updateEnvAttributes` implementation -/
@[export lean_update_env_attributes]
def updateEnvAttributesImpl (env : Environment) : IO Environment := do
  let map ← attributeMapRef.get
  let s := attributeExtension.getState env
  let s := map.foldl (init := s) fun s attrName attrImpl =>
    if s.map.contains attrName then
      s
    else
      { s with map := s.map.insert attrName attrImpl }
  return attributeExtension.setState env s

/-- `getNumBuiltinAttributes` implementation -/
@[export lean_get_num_attributes] def getNumBuiltiAttributesImpl : IO Nat :=
  return (← attributeMapRef.get).size

end Lean

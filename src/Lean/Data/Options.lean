/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich and Leonardo de Moura
-/
module

prelude
public import Lean.ImportingFlag
public import Lean.Data.KVMap
public import Lean.Data.NameMap.Basic

public section

namespace Lean

structure Options where
  private map : NameMap DataValue
  /--
  Whether any option with prefix `trace` is set. This does *not* imply that any of such option is
  set to `true` but it does capture the most common case that no such option has ever been touched.
  -/
  hasTrace : Bool

namespace Options

def empty : Options where
  map := {}
  hasTrace := false

@[export lean_options_get_empty]
private def getEmpty (_ : Unit) : Options := .empty

instance : Inhabited Options where
  default := .empty
instance : ToString Options where
  toString o := private toString o.map.toList
instance [Monad m] : ForIn m Options (Name × DataValue) where
  forIn o init f := private forIn o.map init f
instance : BEq Options where
  beq o1 o2 := private o1.map.beq o2.map
instance : EmptyCollection Options where
  emptyCollection := .empty

@[inline] def find? (o : Options) (k : Name) : Option DataValue :=
  o.map.find? k

@[deprecated find? (since := "2026-01-15")]
def find := find?

@[inline] def get? {α : Type} [KVMap.Value α] (o : Options) (k : Name) : Option α :=
  o.map.find? k |>.bind KVMap.Value.ofDataValue?

@[inline] def get {α : Type} [KVMap.Value α] (o : Options) (k : Name) (defVal : α) : α :=
  o.get? k |>.getD defVal

@[inline] def getBool (o : Options) (k : Name) (defVal : Bool := false) : Bool :=
  o.get k defVal

@[inline] def contains (o : Options) (k : Name) : Bool :=
  o.map.contains k

@[inline] def insert (o : Options) (k : Name) (v : DataValue) : Options where
  map := o.map.insert k v
  hasTrace := o.hasTrace || (`trace).isPrefixOf k

def set {α : Type} [KVMap.Value α] (o : Options) (k : Name) (v : α) : Options :=
  o.insert k (KVMap.Value.toDataValue v)

@[inline] def setBool (o : Options) (k : Name) (v : Bool) : Options :=
  o.set k v

def erase (o : Options) (k : Name) : Options where
  map := o.map.erase k
  -- `erase` is expected to be used even more rarely than `set` so O(n) is fine
  hasTrace := o.map.keys.any (`trace).isPrefixOf

def mergeBy (f : Name → DataValue → DataValue → DataValue) (o1 o2 : Options) : Options where
  map := o1.map.mergeWith f o2.map
  hasTrace := o1.hasTrace || o2.hasTrace

end Options

structure OptionDecl where
  name     : Name
  declName : Name := by exact decl_name%
  defValue : DataValue
  descr    : String := ""
  deriving Inhabited

def OptionDecl.fullDescr (self : OptionDecl) : String := Id.run do
  let mut descr := self.descr
  if (`backward).isPrefixOf self.name then
    unless descr.isEmpty do
      descr := descr ++ "\n\n"
    descr := descr ++ "\
      This is a backwards compatibility option, intended to help migrating to new Lean releases. \
      It may be removed without further notice 6 months after their introduction. \
      Please report an issue if you rely on this option."
  pure descr

@[expose] def OptionDecls := NameMap OptionDecl

instance : Inhabited OptionDecls := ⟨({} : NameMap OptionDecl)⟩

private builtin_initialize optionDeclsRef : IO.Ref OptionDecls ← IO.mkRef (mkNameMap OptionDecl)

@[export lean_register_option]
def registerOption (name : Name) (decl : OptionDecl) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "Failed to register option: Options can only be registered during initialization")
  let decls ← optionDeclsRef.get
  if decls.contains name then
    throw $ IO.userError s!"Invalid option declaration `{name}`: Option already exists"
  optionDeclsRef.set $ decls.insert name decl

def getOptionDecls : IO OptionDecls := optionDeclsRef.get

@[export lean_get_option_decls_array]
def getOptionDeclsArray : IO (Array (Name × OptionDecl)) := do
  let decls ← getOptionDecls
  return decls.foldl
   (fun (r : Array (Name × OptionDecl)) k v => r.push (k, v))
   #[]

def getOptionDecl (name : Name) : IO OptionDecl := do
  let decls ← getOptionDecls
  let (some decl) ← pure (decls.find? name) | throw $ IO.userError s!"Unknown option `{name}`"
  pure decl

def getOptionDefaultValue (name : Name) : IO DataValue := do
  let decl ← getOptionDecl name
  pure decl.defValue

def getOptionDescr (name : Name) : IO String := do
  let decl ← getOptionDecl name
  pure decl.descr

class MonadOptions (m : Type → Type) where
  getOptions : m Options

export MonadOptions (getOptions)

instance [MonadLift m n] [MonadOptions m] : MonadOptions n where
  getOptions := liftM (getOptions : m _)

variable [Monad m] [MonadOptions m]

def getBoolOption (k : Name) (defValue := false) : m Bool := do
  let opts ← getOptions
  return opts.get k defValue

def getNatOption (k : Name) (defValue := 0) : m Nat := do
  let opts ← getOptions
  return opts.get k defValue

class MonadWithOptions (m : Type → Type) where
  withOptions (f : Options → Options) (x : m α) : m α

export MonadWithOptions (withOptions)

instance [MonadFunctor m n] [MonadWithOptions m] : MonadWithOptions n where
  withOptions f x := monadMap (m := m) (withOptions f) x

/-! Remark: `_inPattern` is an internal option for communicating to the delaborator that
   the term being delaborated should be treated as a pattern. -/

def withInPattern [MonadWithOptions m] (x : m α) : m α :=
  withOptions (fun o => o.set `_inPattern true) x

def Options.getInPattern (o : Options) : Bool :=
  o.get `_inPattern false

/-- A strongly-typed reference to an option. -/
protected structure Option (α : Type) where
  name     : Name
  defValue : α
  deriving Inhabited

namespace Option

protected structure Decl (α : Type) where
  defValue : α
  descr    : String := ""

protected def get? [KVMap.Value α] (opts : Options) (opt : Lean.Option α) : Option α :=
  opts.get? opt.name

protected def get [KVMap.Value α] (opts : Options) (opt : Lean.Option α) : α :=
  opts.get opt.name opt.defValue

@[export lean_options_get_bool]
private def getBool (opts : Options) (name : Name) (defValue : Bool) : Bool :=
  opts.get name defValue

protected def getM [Monad m] [MonadOptions m] [KVMap.Value α] (opt : Lean.Option α) : m α :=
  return opt.get (← getOptions)

protected def set [KVMap.Value α] (opts : Options) (opt : Lean.Option α) (val : α) : Options :=
  opts.set opt.name val

@[export lean_options_update_bool]
private def updateBool (opts : Options) (name : Name) (val : Bool) : Options :=
  opts.set name val

/-- Similar to `set`, but update `opts` only if it doesn't already contains an setting for `opt.name` -/
protected def setIfNotSet [KVMap.Value α] (opts : Options) (opt : Lean.Option α) (val : α) : Options :=
  if opts.contains opt.name then opts else opt.set opts val

protected def register [KVMap.Value α] (name : Name) (decl : Lean.Option.Decl α) (ref : Name := by exact decl_name%) : IO (Lean.Option α) := do
  registerOption name {
    name
    declName := ref
    defValue := KVMap.Value.toDataValue decl.defValue
    descr := decl.descr
  }
  return { name := name, defValue := decl.defValue }

macro (name := registerBuiltinOption) doc?:(docComment)? vis?:(visibility)? "register_builtin_option" name:ident " : " type:term " := " decl:term : command =>
  `($[$doc?]? $[$vis?:visibility]? builtin_initialize $name : Lean.Option $type ← Lean.Option.register $(quote name.getId) $decl)

macro (name := registerOption) mods:declModifiers "register_option" name:ident " : " type:term " := " decl:term : command =>
  `($mods:declModifiers initialize $name : Lean.Option $type ← Lean.Option.register $(quote name.getId) $decl)

end Option

end Lean

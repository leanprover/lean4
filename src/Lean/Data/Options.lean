/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich and Leonardo de Moura
-/
import Lean.ImportingFlag
import Lean.Data.KVMap
import Lean.Data.NameMap

namespace Lean

def Options := KVMap

def Options.empty : Options  := {}
instance : Inhabited Options where
  default := {}
instance : ToString Options := inferInstanceAs (ToString KVMap)
instance : ForIn m Options (Name × DataValue) := inferInstanceAs (ForIn _ KVMap _)
instance : BEq Options := inferInstanceAs (BEq KVMap)

structure OptionDecl where
  declName : Name := by exact decl_name%
  defValue : DataValue
  group    : String := ""
  descr    : String := ""
  deriving Inhabited

def OptionDecls := NameMap OptionDecl

instance : Inhabited OptionDecls := ⟨({} : NameMap OptionDecl)⟩

private builtin_initialize optionDeclsRef : IO.Ref OptionDecls ← IO.mkRef (mkNameMap OptionDecl)

@[export lean_register_option]
def registerOption (name : Name) (decl : OptionDecl) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register option, options can only be registered during initialization")
  let decls ← optionDeclsRef.get
  if decls.contains name then
    throw $ IO.userError s!"invalid option declaration '{name}', option already exists"
  optionDeclsRef.set $ decls.insert name decl

def getOptionDecls : IO OptionDecls := optionDeclsRef.get

@[export lean_get_option_decls_array]
def getOptionDeclsArray : IO (Array (Name × OptionDecl)) := do
  let decls ← getOptionDecls
  pure $ decls.fold
   (fun (r : Array (Name × OptionDecl)) k v => r.push (k, v))
   #[]

def getOptionDecl (name : Name) : IO OptionDecl := do
  let decls ← getOptionDecls
  let (some decl) ← pure (decls.find? name) | throw $ IO.userError s!"unknown option '{name}'"
  pure decl

def getOptionDefaultValue (name : Name) : IO DataValue := do
  let decl ← getOptionDecl name
  pure decl.defValue

def getOptionDescr (name : Name) : IO String := do
  let decl ← getOptionDecl name
  pure decl.descr

def setOptionFromString (opts : Options) (entry : String) : IO Options := do
  let ps := (entry.splitOn "=").map String.trim
  let [key, val] ← pure ps | throw $ IO.userError "invalid configuration option entry, it must be of the form '<key> = <value>'"
  let key := Name.mkSimple key
  let defValue ← getOptionDefaultValue key
  match defValue with
  | DataValue.ofString _ => pure $ opts.setString key val
  | DataValue.ofBool _   =>
    if key == `true then pure $ opts.setBool key true
    else if key == `false then pure $ opts.setBool key false
    else throw $ IO.userError s!"invalid Bool option value '{val}'"
  | DataValue.ofName _   => pure $ opts.setName key val.toName
  | DataValue.ofNat _    =>
    match val.toNat? with
    | none   => throw (IO.userError s!"invalid Nat option value '{val}'")
    | some v => pure $ opts.setNat key v
  | DataValue.ofInt _    =>
    match val.toInt? with
    | none   => throw (IO.userError s!"invalid Int option value '{val}'")
    | some v => pure $ opts.setInt key v
  | DataValue.ofSyntax _ => throw (IO.userError s!"invalid Syntax option value")

class MonadOptions (m : Type → Type) where
  getOptions : m Options

export MonadOptions (getOptions)

instance [MonadLift m n] [MonadOptions m] : MonadOptions n where
  getOptions := liftM (getOptions : m _)

variable [Monad m] [MonadOptions m]

def getBoolOption (k : Name) (defValue := false) : m Bool := do
  let opts ← getOptions
  return opts.getBool k defValue

def getNatOption (k : Name) (defValue := 0) : m Nat := do
  let opts ← getOptions
  return opts.getNat k defValue

class MonadWithOptions (m : Type → Type) where
  withOptions (f : Options → Options) (x : m α) : m α

export MonadWithOptions (withOptions)

instance [MonadFunctor m n] [MonadWithOptions m] : MonadWithOptions n where
  withOptions f x := monadMap (m := m) (withOptions f) x

/-! Remark: `_inPattern` is an internal option for communicating to the delaborator that
   the term being delaborated should be treated as a pattern. -/

def withInPattern [MonadWithOptions m] (x : m α) : m α :=
  withOptions (fun o => o.setBool `_inPattern true) x

def Options.getInPattern (o : Options) : Bool :=
  o.getBool `_inPattern

/-- A strongly-typed reference to an option. -/
protected structure Option (α : Type) where
  name     : Name
  defValue : α
  deriving Inhabited

namespace Option

protected structure Decl (α : Type) where
  defValue : α
  group    : String := ""
  descr    : String := ""

protected def get? [KVMap.Value α] (opts : Options) (opt : Lean.Option α) : Option α :=
  opts.get? opt.name

protected def get [KVMap.Value α] (opts : Options) (opt : Lean.Option α) : α :=
  opts.get opt.name opt.defValue

protected def set [KVMap.Value α] (opts : Options) (opt : Lean.Option α) (val : α) : Options :=
  opts.set opt.name val

/-- Similar to `set`, but update `opts` only if it doesn't already contains an setting for `opt.name` -/
protected def setIfNotSet [KVMap.Value α] (opts : Options) (opt : Lean.Option α) (val : α) : Options :=
  if opts.contains opt.name then opts else opt.set opts val

protected def register [KVMap.Value α] (name : Name) (decl : Lean.Option.Decl α) (ref : Name := by exact decl_name%) : IO (Lean.Option α) := do
  registerOption name {
    declName := ref
    defValue := KVMap.Value.toDataValue decl.defValue
    group := decl.group
    descr := decl.descr
  }
  return { name := name, defValue := decl.defValue }

macro (name := registerBuiltinOption) doc?:(docComment)? "register_builtin_option" name:ident " : " type:term " := " decl:term : command =>
  `($[$doc?]? builtin_initialize $name : Lean.Option $type ← Lean.Option.register $(quote name.getId) $decl)

macro (name := registerOption) doc?:(docComment)? "register_option" name:ident " : " type:term " := " decl:term : command =>
  `($[$doc?]? initialize $name : Lean.Option $type ← Lean.Option.register $(quote name.getId) $decl)

end Option

end Lean

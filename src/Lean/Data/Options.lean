#lang lean4
/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich and Leonardo de Moura
-/
import Lean.Data.KVMap

namespace Lean

def Options := KVMap

def Options.empty : Options  := {}
instance : Inhabited Options := ⟨Options.empty⟩
instance : HasToString Options := inferInstanceAs (HasToString KVMap)

structure OptionDecl :=
  (defValue : DataValue)
  (group    : String := "")
  (descr    : String := "")

def OptionDecls := NameMap OptionDecl

instance : Inhabited OptionDecls := ⟨({} : NameMap OptionDecl)⟩

private def initOptionDeclsRef : IO (IO.Ref OptionDecls) :=
  IO.mkRef (mkNameMap OptionDecl)

@[builtinInit initOptionDeclsRef]
private constant optionDeclsRef : IO.Ref OptionDecls := arbitrary _

@[export lean_register_option]
def registerOption (name : Name) (decl : OptionDecl) : IO Unit := do
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

def getOptionDefaulValue (name : Name) : IO DataValue := do
  let decl ← getOptionDecl name
  pure decl.defValue

def getOptionDescr (name : Name) : IO String := do
  let decl ← getOptionDecl name
  pure decl.descr

def setOptionFromString (opts : Options) (entry : String) : IO Options := do
  let ps := (entry.splitOn "=").map String.trim
  let [key, val] ← pure ps | throw $ IO.userError "invalid configuration option entry, it must be of the form '<key> = <value>'"
  let key := mkNameSimple key
  let defValue ← getOptionDefaulValue key
  match defValue with
  | DataValue.ofString v => pure $ opts.setString key val
  | DataValue.ofBool v   =>
    if key == `true then pure $ opts.setBool key true
    else if key == `false then pure $ opts.setBool key false
    else throw $ IO.userError s!"invalid Bool option value '{val}'"
  | DataValue.ofName v   => pure $ opts.setName key val.toName
  | DataValue.ofNat v    =>
    match val.toNat? with
    | none   => throw (IO.userError s!"invalid Nat option value '{val}'")
    | some v => pure $ opts.setNat key v
  | DataValue.ofInt v    =>
    match val.toInt? with
    | none   => throw (IO.userError s!"invalid Int option value '{val}'")
    | some v => pure $ opts.setInt key v

builtin_initialize
  registerOption `verbose {
    defValue := true,
    group := "",
    descr := "disable/enable verbose messages"
  }
  registerOption `timeout {
    defValue := DataValue.ofNat 0,
    group := "",
    descr := "the (deterministic) timeout is measured as the maximum of memory allocations (in thousands) per task, the default is unbounded"
  }
  registerOption `maxMemory {
    defValue := DataValue.ofNat 2048,
    group := "",
    descr := "maximum amount of memory available for Lean in megabytes"
  }

class MonadOptions (m : Type → Type) :=
  (getOptions : m Options)

export MonadOptions (getOptions)

instance (m n) [MonadOptions m] [MonadLift m n] : MonadOptions n :=
  { getOptions := liftM (getOptions : m _) }

variables {m} [Monad m] [MonadOptions m]

def getBoolOption (k : Name) (defValue := false) : m Bool := do
  let opts ← getOptions
  pure $ opts.getBool k defValue

def getNatOption (k : Name) (defValue := 0) : m Nat := do
  let opts ← getOptions
  pure $ opts.getNat k defValue

end Lean

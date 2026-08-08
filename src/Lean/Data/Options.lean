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
import Init.Data.ToString.Macro

public section

namespace Lean

/--
Returns whether the option `name` is observable by type class resolution without affecting its
result: tracing, pretty printing and formatting (of messages and trace nodes, which capture the
ambient options object and are rendered later), profiling, diagnostics, debugging, resource
limits (exceeding them throws, and exceptions are not cached), and the elaboration/kernel
options read by constant realization triggered from the search (whose results are registered in
the environment on first use and thus shared regardless of options).
-/
def isSynthInertOption (name : Name) : Bool :=
  Name.isPrefixOf `trace name || Name.isPrefixOf `pp name || Name.isPrefixOf `format name ||
  Name.isPrefixOf `profiler name || Name.isPrefixOf `diagnostics name ||
  Name.isPrefixOf `debug name || Name.isPrefixOf `Elab name || Name.isPrefixOf `Kernel name ||
  Name.isPrefixOf `interpreter name || Name.isPrefixOf `server name ||
  Name.isPrefixOf `internal name ||
  -- limits: exceeding them throws (`Lean.checkExponent` is reached from `Meta.check` during
  -- cached-result application), and exceptions are not cached
  name == `maxHeartbeats || name == `maxRecDepth ||
  Name.isPrefixOf `exponentiation name ||
  -- pseudo-option marking pattern-printing mode, read by the delaborator when rendering
  -- messages that captured a restricted options object (`Options.getInPattern`)
  name == `_inPattern

/--
Access restriction on an `Options` object, enforced by the by-name accessors (`Options.find?`,
`Options.get?`, `Options.contains` and everything built on them): accessing an option outside
the allowed set panics and behaves as if the option were unset. Restricting is a constant-time
flag update (`Options.restrict`) that keeps the underlying entries, so iteration (e.g. `ForIn`)
is unaffected.
-/
inductive OptionsRestriction where
  /-- No restriction. -/
  | none
  /--
  Only inert options (`isSynthInertOption`) may be read by name: type class resolution records
  every result-relevant option lookup as a dependency of the cache entry it is computing (see
  `Lean.Meta.getRecordedOption`), so reads on the search path must go through the recording
  accessors, which bypass this restriction via `Options.findUnrestricted?`. A pure by-name read
  under this restriction is an unrecorded access and panics.
  -/
  | tcResolution

/-- Returns whether accessing the option `name` is allowed under the restriction. -/
def OptionsRestriction.allows : OptionsRestriction → Name → Bool
  | .none, _ => true
  | .tcResolution, name => isSynthInertOption name

structure Options where
  private map : NameMap DataValue
  /--
  Whether any option with prefix `trace` is set. This does *not* imply that any of such option is
  set to `true` but it does capture the most common case that no such option has ever been touched.
  -/
  hasTrace : Bool
  /-- Access restriction enforced by the by-name accessors; see `OptionsRestriction`. -/
  restriction : OptionsRestriction := .none

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

/--
Reads the raw entry for `k`, bypassing the access restriction. Callers are responsible for
recording the access as a dependency where required; see `OptionsRestriction.tcResolution` and
`Lean.Meta.getRecordedOption`.
-/
@[inline] def findUnrestricted? (o : Options) (k : Name) : Option DataValue :=
  o.map.find? k

@[inline] def find? (o : Options) (k : Name) : Option DataValue :=
  if o.restriction.allows k then
    o.map.find? k
  else
    panic! s!"unrecorded access to option `{k}` under the current options restriction; \
      reads on the type class resolution path must use the recording accessors, \
      see `Lean.OptionsRestriction`"

@[deprecated find? (since := "2026-01-15")]
def find := find?

@[inline] def get? {α : Type} [KVMap.Value α] (o : Options) (k : Name) : Option α :=
  o.find? k |>.bind KVMap.Value.ofDataValue?

@[inline] def get {α : Type} [KVMap.Value α] (o : Options) (k : Name) (defVal : α) : α :=
  o.get? k |>.getD defVal

@[inline] def getBool (o : Options) (k : Name) (defVal : Bool := false) : Bool :=
  o.get k defVal

@[inline] def contains (o : Options) (k : Name) : Bool :=
  if o.restriction.allows k then
    o.map.contains k
  else
    panic! s!"unrecorded access to option `{k}` under the current options restriction; \
      reads on the type class resolution path must use the recording accessors, \
      see `Lean.OptionsRestriction`"

/-- Restricts by-name access to the options allowed by `r`; see `OptionsRestriction`. -/
@[inline] def restrict (o : Options) (r : OptionsRestriction) : Options :=
  { o with restriction := r }

@[inline] def insert (o : Options) (k : Name) (v : DataValue) : Options where
  map := o.map.insert k v
  hasTrace := o.hasTrace || (`trace).isPrefixOf k
  restriction := o.restriction

def set {α : Type} [KVMap.Value α] (o : Options) (k : Name) (v : α) : Options :=
  o.insert k (KVMap.Value.toDataValue v)

@[inline] def setBool (o : Options) (k : Name) (v : Bool) : Options :=
  o.set k v

def erase (o : Options) (k : Name) : Options where
  map := o.map.erase k
  -- `erase` is expected to be used even more rarely than `set` so O(n) is fine
  hasTrace := o.map.keys.any (`trace).isPrefixOf
  restriction := o.restriction

def mergeBy (f : Name → DataValue → DataValue → DataValue) (o1 o2 : Options) : Options where
  map := o1.map.mergeWith f o2.map
  hasTrace := o1.hasTrace || o2.hasTrace
  restriction := o1.restriction

end Options

structure OptionDeprecation where
  since    : String
  text?    : Option String := none
  /-- The option to use instead, taken from the `@[deprecated <name>]` attribute. -/
  newName? : Option Name := none
  deriving Inhabited

structure OptionDecl where
  name     : Name
  declName : Name := by exact decl_name%
  defValue : DataValue
  descr    : String := ""
  deprecation? : Option OptionDeprecation := none
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
  deprecation? : Option OptionDeprecation := none

/--
Reads the option bypassing the access restriction, without recording the access; only for reads
that provably cannot influence a type class resolution cache entry, e.g. limits whose exceedance
throws (exceptions are not cached). See `OptionsRestriction.tcResolution`.
-/
protected def getUnrestricted [KVMap.Value α] (opts : Options) (opt : Lean.Option α) : α :=
  ((opts.findUnrestricted? opt.name).bind KVMap.Value.ofDataValue?).getD opt.defValue

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
    deprecation? := decl.deprecation?
  }
  return { name := name, defValue := decl.defValue }

macro (name := registerBuiltinOption) doc?:(docComment)? vis?:(visibility)? "register_builtin_option" name:ident " : " type:term " := " decl:term : command =>
  `($[$doc?]? $[$vis?:visibility]? builtin_initialize $name : Lean.Option $type ← Lean.Option.register $(quote name.getId) $decl)

private meta def declWithDeprecation (attr : Syntax) (type decl : Term) : MacroM Term := do
  let `(attr| deprecated $[$id?]? $[$text?]? $[$_typeChanged?]? $[(since := $since?)]?) := attr | return decl
  let since : Term ← match since? with | some s => pure s | none => `("")
  let text : Term ← match text? with | some text => `(some $text) | none => `(none)
  let newName : Term ← match id? with | some id => `(some ($id).name) | none => `(none)
  `({ ($decl : Lean.Option.Decl $type) with
      deprecation? := some { since := $since, text? := $text, newName? := $newName } })

macro (name := registerOption) mods:declModifiers "register_option" name:ident " : " type:term " := " decl:term : command => do
  let attr? := mods.raw.find? (·.isOfKind ``Lean.deprecated)
  -- The `deprecation?` field is internal: it is populated from the `@[deprecated]` attribute below.
  let field? := decl.raw.find? (·.getId == `deprecation?)
  let decl ← match attr?, field? with
    | some _, some field =>
      Macro.throwErrorAt field "remove the `deprecation?` field: it is populated automatically from \
        the option's `@[deprecated]` attribute"
    | none, some field =>
      Macro.throwErrorAt field "do not set the `deprecation?` field directly; it is an internal \
        implementation detail. Deprecate the option with a `@[deprecated \"...\" (since := \"...\")]` \
        attribute instead"
    | some attr, none => declWithDeprecation attr type decl
    | none, none => pure decl
  `($mods:declModifiers initialize $name : Lean.Option $type ← Lean.Option.register $(quote name.getId) $decl)

end Option

end Lean

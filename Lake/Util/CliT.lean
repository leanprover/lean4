/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

--------------------------------------------------------------------------------
-- # CLI Transformer Definition
--------------------------------------------------------------------------------

-- Involves trickery patterned after `MacroM`
-- to allow `CliMethods` to refer to `CliT`

constant CliMethodsRefPointed (m : Type → Type v) : PointedType.{0}
def CliMethodsRef (m : Type → Type v) : Type := (CliMethodsRefPointed m).type

abbrev CliT (m : Type → Type v) :=
  ReaderT (CliMethodsRef m) <| StateT (List String) m

instance [Pure m] [Inhabited α] : Inhabited (CliT m α) :=
  ⟨fun _ _ => pure (Inhabited.default, Inhabited.default)⟩

structure CliMethods (m : Type → Type v) where
  longOption : String → CliT m PUnit
  longShortOption : String → CliT m PUnit
  shortOption : Char → CliT m PUnit

instance [Pure m] : Inhabited (CliMethods m) :=
  ⟨Inhabited.default, Inhabited.default, Inhabited.default⟩

namespace CliMethodsRef

unsafe def mkImp (methods : CliMethods m) : CliMethodsRef m :=
  unsafeCast methods

@[implementedBy mkImp]
constant mk (methods : CliMethods m) : CliMethodsRef m :=
  (CliMethodsRefPointed m).val

instance : Coe (CliMethods m) (CliMethodsRef m) := ⟨mk⟩
instance [Pure m] : Inhabited (CliMethodsRef m) := ⟨mk Inhabited.default⟩

unsafe def getImp [Pure m] (self : CliMethodsRef m) : CliMethods m :=
  unsafeCast self

@[implementedBy getImp]
constant get [Pure m] (self : CliMethodsRef m) : CliMethods m

end CliMethodsRef

--------------------------------------------------------------------------------
-- # CLI Utilities
--------------------------------------------------------------------------------

namespace CliT
variable [Monad m]

/-- Run the CLI on the given argument list using the given methods. -/
def run (self : CliT m α) (args : List String) (methods : CliMethods m) : m α :=
  ReaderT.run self methods |>.run' args

/-- Get the remaining argument list. -/
def getArgs : CliT m (List String) :=
  get

/-- Replace the argument list. -/
def setArgs (args : List String) : CliT m PUnit :=
  set args

/-- Take the head of the remaining argument list (or none if empty). -/
def takeArg? : CliT m (Option String) :=
  modifyGet fun | [] => (none, []) | arg :: args => (some arg, args)

/-- Take the remaining argument list, leaving only an empty list. -/
def takeArgs : CliT m (List String) :=
  modifyGet fun args => (args, [])

/-- Add a string to the head of the remaining argument list. -/
def consArg (arg : String) : CliT m PUnit :=
  modify fun args => arg :: args

/-- Get the methods of this CLI. -/
def getMethods : CliT m (CliMethods m) :=
  (·.get) <$> read

/-- Change the methods of this CLI. -/
def adaptMethods (f : CliMethods m → CliMethods m) (self : CliT m α) : CliT m α :=
  self.adapt fun ref => CliMethodsRef.mk <| f ref.get

/-- Process a short option (ex. `-x` or `--`). -/
def shortOption (opt : Char) : CliT m PUnit :=
  getMethods >>= (·.shortOption opt)

/-- Process a short option of the form `-x=arg`. -/
def shortOptionEq (opt : String) : CliT m PUnit := do
  consArg (opt.drop 3); shortOption opt[1]

/-- Process a short option of the form `-xarg`. -/
def shortOptionArg (opt : String) : CliT m PUnit := do
  consArg (opt.drop 2); shortOption opt[1]

/-- Process a short option of the form `"-x arg"`. -/
def shortOptionSpace (opt : String) : CliT m PUnit := do
  consArg <| opt.drop 2 |>.trimLeft; shortOption opt[1]

/-- Process a multiple short options grouped together (ex. `-xyz` as `x`, `y`, `z`). -/
def multiShortOption (opt : String) : CliT m PUnit := do
  for i in [1:opt.length] do shortOption opt[i]

/-- Process a long option (ex. `--long` or `"--long a1 a2"`). -/
def longOption (opt : String) : CliT m PUnit  := do
  getMethods >>= (·.longOption opt)

/-- Process a long short option (ex. `-long`, `-xarg`, `-xyz`). -/
def longShortOption (opt : String) : CliT m PUnit := do
  getMethods >>= (·.longShortOption opt)

/--
  Process an option, short or long.
  An option is an argument of length > 1 starting with a dash (`-`).
  An option may consume additional elements of the argument list.
-/
def option (opt : String) : CliT m PUnit :=
  if opt[1] == '-' then -- `--(.*)`
    longOption opt
  else
    if opt.length == 2 then -- `-x`
      shortOption opt[1]
    else -- `-c(.+)`
      match opt[2] with
      | '=' => -- `-x=arg`
        shortOptionEq opt
      | ' ' => -- `"-x arg"`
        shortOptionSpace opt
      | _   => -- `-long`
        longShortOption opt

/-- Process the leading options of the remaining argument list. -/
partial def processLeadingOptions : CliT m PUnit := do
  match (← getArgs) with
  | [] => pure ()
  | arg :: args =>
    let len := arg.length
    if len > 1 && arg[0] == '-' then -- `-(.+)`
      setArgs args
      option arg
      processLeadingOptions
    else if len == 0 then -- skip empty leading args
      setArgs args
      processLeadingOptions

/-- Process every option and collect the remaining arguments into the given `Array`. -/
partial def collectArgsInto (arr : Array String) : CliT m (Array String) := do
  processLeadingOptions
  match (← takeArg?) with
  | some arg => collectArgsInto (arr.push arg)
  | none => arr

/-- Process every option and collect the remaining arguments into an `Array`. -/
def collectArgs : CliT m (Array String) :=
  collectArgsInto #[]

/-- Process every option in the argument list. -/
def processOptions : CliT m PUnit := do
  setArgs (← collectArgs).toList

end CliT

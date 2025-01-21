/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Data.Array.Basic

namespace Lake

/-!
Defines the abstract CLI interface for Lake.
-/

/-! # Types -/

def ArgList := List String

@[inline] def ArgList.mk (args : List String) : ArgList :=
  args

abbrev ArgsT := StateT ArgList

@[inline] def ArgsT.run (args : List String) (self : ArgsT m α) : m (α × List String) :=
  StateT.run self args

@[inline] def ArgsT.run' [Functor m] (args : List String) (self : ArgsT m α) : m α :=
  StateT.run' self args

structure OptionHandlers (m : Type u → Type v) (α : Type u) where
  /-- Process a long option (ex. `--long` or `"--long foo bar"`). -/
  long : String → m α
  /-- Process a short option (ex. `-x` or `--`). -/
  short : Char → m α
  /-- Process a long short option (ex. `-long`, `-xarg`, `-xyz`). -/
  longShort : String → m α

/-! # Utilities -/

variable [Monad m] [MonadStateOf ArgList m]

/-- Get the remaining argument list. -/
@[inline] def getArgs : m (List String) :=
  get

/-- Replace the argument list. -/
@[inline] def setArgs (args : List String) : m PUnit :=
  set (ArgList.mk args)

/-- Take the head of the remaining argument list (or none if empty). -/
@[inline] def takeArg? : m (Option String) :=
  modifyGet fun | [] => (none, []) | arg :: args => (some arg, args)

/-- Take the head of the remaining argument list (or `default` if none). -/
@[inline] def takeArgD (default : String) : m String :=
  modifyGet fun | [] => (default, []) | arg :: args => (arg, args)

/-- Take the remaining argument list, leaving only an empty list. -/
@[inline] def takeArgs : m (List String) :=
  modifyGet fun args => (args, [])

/-- Add a string to the head of the remaining argument list. -/
@[inline] def consArg (arg : String) : m PUnit :=
  modify fun args => arg :: args

/-- Process a short option of the form `-x=arg`. -/
@[inline] def shortOptionWithEq (handle : Char → m α) (opt : String) : m α := do
  consArg (opt.drop 3); handle (opt.get ⟨1⟩)

/-- Process a short option of the form `"-x arg"`. -/
@[inline] def shortOptionWithSpace (handle : Char → m α) (opt : String) : m α := do
  consArg <| opt.drop 2 |>.trimLeft; handle (opt.get ⟨1⟩)

/-- Process a short option of the form `-xarg`. -/
@[inline] def shortOptionWithArg (handle : Char → m α) (opt : String) : m α := do
  consArg (opt.drop 2); handle (opt.get ⟨1⟩)

/-- Process a multiple short options grouped together (ex. `-xyz` as `x`, `y`, `z`). -/
@[inline] def multiShortOption (handle : Char → m PUnit) (opt : String) : m PUnit := do
  let rec loop (p : String.Pos) := do
    if h : opt.atEnd p then
      return
    else
      handle (opt.get' p h)
      loop (opt.next' p h)
  termination_by opt.utf8ByteSize - p.byteIdx
  decreasing_by
    simp [String.atEnd] at h
    apply Nat.sub_lt_sub_left h
    simp [String.lt_next opt p]
  loop ⟨1⟩

/-- Splits a long option of the form `"--long foo bar"` into `--long` and `"foo bar"`. -/
@[inline] def longOptionOrSpace (handle : String → m α) (opt : String) : m α :=
  let pos := opt.posOf ' '
  if pos = opt.endPos then
    handle opt
  else do
    consArg <| opt.extract (opt.next pos) opt.endPos
    handle <| opt.extract 0 pos

/-- Splits a long option of the form `--long=arg` into `--long` and `arg`. -/
@[inline] def longOptionOrEq (handle : String → m α) (opt : String) : m α :=
  let pos := opt.posOf '='
  if pos = opt.endPos then
    handle opt
  else do
    consArg <| opt.extract (opt.next pos) opt.endPos
    handle <| opt.extract 0 pos

/-- Process a long option  of the form `--long`, `--long=arg`, `"--long arg"`. -/
@[inline] def longOption (handle : String → m α) : String → m α :=
  longOptionOrEq <| longOptionOrSpace handle

/-- Process a short option of the form `-x`, `-x=arg`, `-x arg`, or `-long`. -/
@[inline] def shortOption
  (shortHandle : Char → m α) (longHandle : String → m α)
  (opt : String)
: m α :=
  if opt.length == 2 then -- `-x`
    shortHandle (opt.get ⟨1⟩)
  else -- `-c(.+)`
    match opt.get ⟨2⟩ with
    | '=' => -- `-x=arg`
      shortOptionWithEq shortHandle opt
    | ' ' => -- `"-x arg"`
      shortOptionWithSpace shortHandle opt
    | _   => -- `-long`
      longHandle opt

/--
Process an option, short or long, using the given handlers.
An option is an argument of length > 1 starting with a dash (`-`).
An option may consume additional elements of the argument list.
-/
@[inline] def option (handlers : OptionHandlers m α) (opt : String) : m α :=
  if opt.get ⟨1⟩ == '-' then -- `--(.*)`
    longOption handlers.long opt
  else
    shortOption handlers.short handlers.longShort opt

/-- Process the head argument of the list using `handle` if it is an option. -/
def processLeadingOption (handle : String → m PUnit) : m PUnit := do
  match (← getArgs) with
  | [] => pure ()
  | arg :: args =>
    if arg.length > 1 && arg.get 0 == '-' then -- `-(.+)`
      setArgs args
      handle arg

/--
Process the leading options of the remaining argument list.
Consumes empty leading arguments in the argument list.
-/
partial def processLeadingOptions (handle : String → m PUnit) : m PUnit := do
  if let arg :: args ← getArgs then
    let len := arg.length
    if len > 1 && arg.get 0 == '-' then -- `-(.+)`
      setArgs args
      handle arg
      processLeadingOptions handle
    else if len == 0 then -- skip empty leading args
      setArgs args
      processLeadingOptions handle

/-- Process every option and collect the remaining arguments into an `Array`. -/
partial def collectArgs
  (option : String → m PUnit) (args : Array String := #[])
: m (Array String) := do
  if let some arg ← takeArg? then
    let len := arg.length
    if len > 1 && arg.get 0 == '-' then -- `-(.+)`
      option arg
      collectArgs option args
    else if len == 0 then -- skip empty args
      collectArgs option args
    else
      collectArgs option (args.push arg)
  else
    pure args

/-- Process every option in the argument list. -/
@[inline] def processOptions (handle : String → m PUnit) : m PUnit := do
  setArgs (← collectArgs handle).toList

/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
import Init.Data.Array.Basic
public import Init.Data.String.TakeDrop
import Init.Data.String.Slice
public import Init.Data.String.Search

namespace Lake

/-!
Defines the abstract CLI interface for Lake.
-/

/-! # Types -/

@[expose]  -- for codegen
public def ArgList := List String

@[inline] public def ArgList.mk (args : List String) : ArgList :=
  args

public abbrev ArgsT := StateT ArgList

@[inline] public def ArgsT.run (args : List String) (self : ArgsT m α) : m (α × List String) :=
  StateT.run self args

@[inline] public def ArgsT.run' [Functor m] (args : List String) (self : ArgsT m α) : m α :=
  StateT.run' self args

public structure OptionHandlers (m : Type u → Type v) (α : Type u) where
  /-- Process a long option (ex. `--long` or `"--long foo bar"`). -/
  long : String → m α
  /-- Process a short option (ex. `-x` or `--`). -/
  short : Char → m α
  /-- Process a long short option (ex. `-long`, `-xarg`, `-xyz`). -/
  longShort : String → m α

/-! # Utilities -/

variable [Monad m] [MonadStateOf ArgList m]

/-- Get the remaining argument list. -/
@[inline] public def getArgs : m (List String) :=
  get

/-- Replace the argument list. -/
@[inline] public def setArgs (args : List String) : m PUnit :=
  set (ArgList.mk args)

/-- Take the head of the remaining argument list (or none if empty). -/
@[inline] public def takeArg? : m (Option String) :=
  modifyGet fun | [] => (none, []) | arg :: args => (some arg, args)

/-- Take the head of the remaining argument list (or `default` if none). -/
@[inline] public def takeArgD (default : String) : m String :=
  modifyGet fun | [] => (default, []) | arg :: args => (arg, args)

/-- Take the remaining argument list, leaving only an empty list. -/
@[inline] public def takeArgs : m (List String) :=
  modifyGet fun args => (args, [])

/-- Add a string to the head of the remaining argument list. -/
@[inline] public def consArg (arg : String) : m PUnit :=
  modify fun args => arg :: args

/-- Process a short option of the form `-x=arg`. -/
@[inline] public def shortOptionWithEq (handle : Char → m α) (opt : String) : m α := do
  consArg (opt.drop 3).copy; handle (String.Pos.Raw.get opt ⟨1⟩)

/-- Process a short option of the form `"-x arg"`. -/
@[inline] public def shortOptionWithSpace (handle : Char → m α) (opt : String) : m α := do
  consArg <| opt.drop 2 |>.trimAsciiStart |>.copy; handle (String.Pos.Raw.get opt ⟨1⟩)

/-- Process a short option of the form `-xarg`. -/
@[inline] public def shortOptionWithArg (handle : Char → m α) (opt : String) : m α := do
  consArg (opt.drop 2).copy; handle (String.Pos.Raw.get opt ⟨1⟩)

/-- Process a multiple short options grouped together (ex. `-xyz` as `x`, `y`, `z`). -/
@[inline] public def multiShortOption (handle : Char → m PUnit) (opt : String) : m PUnit := do
  let rec loop (p : String.Pos.Raw) := do
    if h : p.atEnd opt then
      return
    else
      handle (p.get' opt h)
      loop (p.next' opt h)
  termination_by opt.utf8ByteSize - p.byteIdx
  decreasing_by
    simp [String.Pos.Raw.atEnd] at h
    apply Nat.sub_lt_sub_left h
    exact String.Pos.Raw.byteIdx_lt_byteIdx_next opt p
  loop ⟨1⟩

/-- Splits a long option of the form `"--long foo bar"` into `--long` and `"foo bar"`. -/
@[inline] public def longOptionOrSpace (handle : String → m α) (opt : String) : m α :=
  let pos := opt.find ' '
  if h : pos = opt.endPos then
    handle opt
  else do
    consArg <| opt.extract (pos.next h) opt.endPos
    handle <| opt.extract opt.startPos pos

/-- Splits a long option of the form `--long=arg` into `--long` and `arg`. -/
@[inline] public def longOptionOrEq (handle : String → m α) (opt : String) : m α :=
  let pos := opt.find '='
  if h : pos = opt.endPos then
    handle opt
  else do
    consArg <| opt.extract (pos.next h) opt.endPos
    handle <| opt.extract opt.startPos pos

/-- Process a long option  of the form `--long`, `--long=arg`, `"--long arg"`. -/
@[inline] public def longOption (handle : String → m α) : String → m α :=
  longOptionOrEq <| longOptionOrSpace handle

/-- Process a short option of the form `-x`, `-x=arg`, `-x arg`, or `-long`. -/
@[inline] public def shortOption
  (shortHandle : Char → m α) (longHandle : String → m α)
  (opt : String)
: m α :=
  if opt.length == 2 then -- `-x`
    shortHandle (String.Pos.Raw.get opt ⟨1⟩)
  else -- `-c(.+)`
    match String.Pos.Raw.get opt ⟨2⟩ with
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
@[inline] public def option (handlers : OptionHandlers m α) (opt : String) : m α :=
  if String.Pos.Raw.get opt ⟨1⟩ == '-' then -- `--(.*)`
    longOption handlers.long opt
  else
    shortOption handlers.short handlers.longShort opt

/-- Process the head argument of the list using `handle` if it is an option. -/
public def processLeadingOption (handle : String → m PUnit) : m PUnit := do
  match (← getArgs) with
  | [] => pure ()
  | arg :: args =>
    if arg.length > 1 && String.Pos.Raw.get arg 0 == '-' then -- `-(.+)`
      setArgs args
      handle arg

/--
Process the leading options of the remaining argument list.
Consumes empty leading arguments in the argument list.
-/
public partial def processLeadingOptions (handle : String → m PUnit) : m PUnit := do
  if let arg :: args ← getArgs then
    let len := arg.length
    if len > 1 && String.Pos.Raw.get arg 0 == '-' then -- `-(.+)`
      setArgs args
      handle arg
      processLeadingOptions handle
    else if len == 0 then -- skip empty leading args
      setArgs args
      processLeadingOptions handle

/-- Process every option and collect the remaining arguments into an `Array`. -/
public partial def collectArgs
  (option : String → m PUnit) (args : Array String := #[])
: m (Array String) := do
  if let some arg ← takeArg? then
    let len := arg.length
    if len > 1 && String.Pos.Raw.get arg 0 == '-' then -- `-(.+)`
      option arg
      collectArgs option args
    else if len == 0 then -- skip empty args
      collectArgs option args
    else
      collectArgs option (args.push arg)
  else
    pure args

/-- Process every option in the argument list. -/
@[inline] public def processOptions (handle : String → m PUnit) : m PUnit := do
  setArgs (← collectArgs handle).toList

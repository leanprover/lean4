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

set_option doc.verso true
set_option linter.missingDocs true

/-! # Lake's CLI API

The abstract API used by Lake to parse command line arguments.
-/

namespace Lake

/-! ## Argument-related Types -/

/-- A List of command line arguments. -/
@[expose] -- for codegen
public def ArgList := List String

/-- Type class for monads equipped with a command line argument list. -/
public abbrev MonadArgs (m) := MonadStateOf ArgList m

/-- A monad transformer to equip a monad with an argument list. -/
public abbrev ArgsT := StateT ArgList

/-- Run the monad with the command line arguments {lean}`args`. -/
@[inline] public def ArgsT.run (args : List String) (self : ArgsT m α) : m (α × List String) :=
  StateT.run self args

/-- Run the monad with the command line arguments {lean}`args` and discard any unprocessed arguments. -/
@[inline] public def ArgsT.run' [Functor m] (args : List String) (self : ArgsT m α) : m α :=
  StateT.run' self args

/-- A monadic callback for an arbitrary command line argument. -/
@[expose] -- for codegen
public def ArgHandler (m : Type u → Type v) (α : Type u := PUnit) :=
  (arg : String) → m α

/-- Constructs an argument handler from a monadic function operating on an arbitrary string. -/
@[inline] public def ArgHandler.ofFn (fn : String → m α) : ArgHandler m α :=
  fn

/-! ## Monadic Argument Utilities -/

/-- Gets the remaining argument list. -/
@[inline] public def getArgs [MonadArgs m] : m (List String) :=
  get

/-- Replaces the argument list. -/
@[inline] public def setArgs [MonadArgs m] (args : List String) : m PUnit :=
  set (σ := ArgList) args

/-- Removes and returns the head of the remaining argument list (or {lean}`none` if empty). -/
@[inline] def takeRawArg? [MonadArgs m] : m (Option String) :=
  modifyGet fun | [] => (none, []) | arg :: args => (some arg, args)

/-- Removes and returns  the head of the remaining argument list (or {lean}`default` if empty). -/
@[inline] def takeRawArgD [MonadArgs m] (default : String) : m String :=
  modifyGet fun | [] => (default, []) | arg :: args => (arg, args)

/-- Removes and returns  the remaining argument list, leaving only an empty list. -/
@[inline] public def takeArgs [MonadArgs m] : m (List String) :=
  modifyGet fun args => (args, [])

/-! ## Monadic Argument Parsing Utilities -/

/-- Type class for parsing command line arguments. -/
public class MonadParseArg (α : Type u) (m : Type u → Type v) where
  /-- Parse a command line argument {lean}`arg` into the type {lean}`α`. -/
  parseArg (arg : String.Slice) : m α

export MonadParseArg (parseArg)

public instance [MonadLift m n] [MonadParseArg α  m] : MonadParseArg α n where
  parseArg arg := liftM (m := m) <| parseArg arg

public instance [Pure m] : MonadParseArg String m := ⟨(pure ·.copy)⟩
@[default_instance] public instance [Pure m] : MonadParseArg String.Slice m := ⟨(pure ·)⟩

/-- Type class for indicating a missing argument. -/
public class MonadThrowExpectedArg  (m : Type u → Type v) where
  /-- Throw an error indicating a missing argument described by {lean}`descr`. -/
  throwExpectedArg {α} (descr : String) : m α

export MonadThrowExpectedArg (throwExpectedArg)

public instance [MonadLift m n] [MonadThrowExpectedArg m] : MonadThrowExpectedArg n where
  throwExpectedArg descr := liftM (m := m) <| throwExpectedArg descr

/--
Removes and returns the head of the remaining argument list, parsing the argument into {lean}`α`.

If no argument is available, returns {lean}`none`.
-/
@[inline] public def takeArg?
  [Monad m] [MonadArgs m] [MonadParseArg α m]
: m (Option α) := do
  if let some arg ← takeRawArg? then
    return some (← parseArg arg)
  else
    return none

/--
Removes and returns the head of the remaining argument list, parsing the argument into {lean}`α`.

If no argument is available, returns {lean}`default`.
-/
@[inline] public def takeArgD
  [Monad m] [MonadArgs m] [MonadParseArg α m] (default : α)
: m α := return (← takeArg?).getD default

/--
Removes and returns the head of the remaining argument list, parsing the argument into {lean}`α`.

If no argument is available,, errors using {name}`throwExpectedArg` with {lean}`descr`.
-/
@[inline] public def takeArg
  [Monad m] [MonadArgs m] [MonadParseArg α m] [MonadThrowExpectedArg m] (descr : String)
: m α := do
  if let some arg ← takeArg? then
    parseArg arg
  else
    throwExpectedArg descr

/-! ## Option-related Types -/

/--
{lean}`IsOpt arg` holds if {lean}`arg` is an command line option.
That is, {lean}`arg` is of the form `-(.+)`.
-/
public structure IsOpt (arg : String) : Prop where
  startPos_ne_endPos : arg.startPos ≠ arg.endPos
  get_startPos : arg.startPos.get startPos_ne_endPos = '-'
  next_startPos_ne_endPos : arg.startPos.next startPos_ne_endPos ≠ arg.endPos

namespace IsOpt

/-- A decision procedure for determining if {lean}`arg` is an option. -/
public def dec (arg : String) : Decidable (IsOpt arg) :=
  if h0 : arg.startPos = arg.endPos then
    isFalse (fun ⟨_, _, _⟩ => by contradiction)
  else
    if hc : arg.startPos.get h0 = '-' then
      if h1 : arg.startPos.next h0 = arg.endPos then
        isFalse (fun ⟨_, _, _⟩ => by contradiction)
      else
        isTrue ⟨h0, hc, h1⟩
    else
      isFalse (fun ⟨_, _, _⟩ => by contradiction)

public instance instDecidable {arg : String} : Decidable (IsOpt arg) := dec arg

public theorem offset_next_startPos (h : IsOpt arg) :
  (arg.startPos.next h.startPos_ne_endPos).offset = ⟨1⟩
:= by simp [String.Pos.Raw.ext_iff, h.get_startPos, Char.utf8Size]

/--
The position in {lean}`arg` after the initial {lit}`-`
(e.g., {lit}`x` in {lit}`-x` or {lit}`-` in {lit}`--long`).
-/
@[inline] public def shortPos (h : IsOpt arg) : arg.Pos :=
  arg.pos ⟨1⟩ <| by
    rw [← h.offset_next_startPos]
    apply String.Pos.isValid

public theorem shortPos_eq (h : IsOpt arg) :
  h.shortPos = arg.startPos.next h.startPos_ne_endPos
:= by simp [shortPos, String.Pos.ext_iff, -String.Pos.offset_next, h.offset_next_startPos]

public theorem shortPos_ne_endPos (h : IsOpt arg) : h.shortPos ≠ arg.endPos := by
  rw [shortPos_eq]
  exact h.next_startPos_ne_endPos

/-- The character in {lean}`arg` after the initial {lit}`-`. -/
@[inline] public def shortChar (h : IsOpt arg) : Char :=
  h.shortPos.get h.shortPos_ne_endPos

/-- The position in {lean}`arg` after {lean}`shortChar` (e.g., {lit}`y` in {lit}`-xy`). -/
@[inline] public def afterShortPos (h : IsOpt arg) : arg.Pos :=
  h.shortPos.next h.shortPos_ne_endPos

public theorem afterShortPos_eq (h : IsOpt arg) :
  h.afterShortPos = h.shortPos.next h.shortPos_ne_endPos
:= by rfl

/-- The first two characters of {lean}`arg` (e.g., {lit}`-x` in {lit}`-x=arg`). -/
@[inline] public def shortOpt (h : IsOpt arg) : String.Slice :=
  arg.sliceTo h.afterShortPos

public theorem shortOpt_eq (h : IsOpt arg) :
  h.shortOpt = arg.sliceTo h.afterShortPos
:= by rfl

/-- The remainder of {lean}`arg` after {lean}`shortChar` (e.g., {lit}`=arg` in {lit}`-x=arg`). -/
@[inline] public def shortTail (h : IsOpt arg) : String.Slice :=
  arg.sliceFrom h.afterShortPos

public theorem shortTail_eq (h : IsOpt arg) :
  h.shortTail = arg.sliceFrom h.afterShortPos
:= by rfl

end IsOpt

/-- An optional command line option argument. -/
@[expose] -- for codegen
public def OptArg := Option String.Slice

/-- A monad transformer to equip a monad with an optional command line option argument. -/
public abbrev OptArgT := ReaderT OptArg

/-- Run the monad with the optional command line option argument {lean}`optArg?`. -/
@[inline] public def OptArgT.run (optArg? : Option String.Slice) (self : OptArgT m α) : m α :=
  ReaderT.run self optArg?

/-- Type class for monads equipped with an optional command line option argument. -/
public abbrev MonadOptArg (m) := MonadReaderOf OptArg m

/-- A command line option. -/
@[expose] -- for codegen
public def Opt := String.Slice

/-- Type class for monads equipped with an command line option. -/
public abbrev MonadOpt (m) := MonadReaderOf Opt m

/-- A monad transformer to equip a monad with a command line option and optional argument. -/
public abbrev OptT (m) := ReaderT Opt <| OptArgT m

/-- Run the monad with the command line option {lean}`opt` with optional argument {lean}`optArg?`. -/
@[inline] public def OptT.run
  (opt : String.Slice) (optArg? : Option String.Slice)  (self : OptT m α)
: m α := self opt optArg?

/-- The character of a command line short option (e.g., {lit}`x` of {lit}`-x`). -/
@[expose] -- for codegen
public def OptChar := Char

/-- Type class for monads equipped with a command line short option. -/
public abbrev MonadOptChar (m) := MonadReaderOf OptChar m

/-- A monad transformer to equip a monad with a short option and optional argument. -/
public abbrev ShortOptT (m) := ReaderT OptChar <| OptT m

/-! ## Monadic Option Utilities -/

/-- Get the command line option of the current context (e.g., in an option handler). -/
@[inline] public def getOpt [MonadOpt m] : m String.Slice :=
  read

/--
Get the character of the command line short option of the current context
(e.g., in an option handler).
-/
@[inline] public def getOptChar [MonadOptChar m] : m Char :=
  read

/-- Get the option argument (if any). -/
@[inline] def getOptArg? [MonadOptArg m] : m (Option String.Slice) :=
  read

/--
Returns the option argument or, if {lean}`none`, removes and returns
the head of the remaining argument list.

Parses the argument into {lean}`α`.
If no argument is available, errors using {name}`throwExpectedArg` with {lean}`descr`.
-/
@[inline] public def takeOptArg
  [Monad m] [MonadOptArg m] [MonadArgs m]
  [MonadParseArg α m] [MonadThrowExpectedArg m]
  (descr : String)
: m α := do
  if let some arg ← getOptArg? then
    parseArg arg
  else if let some arg ← takeArg? then
    parseArg arg
  else
    throwExpectedArg descr

/-! ## Option Handler Types -/

/-- A monadic callback for an arbitrary option (e.g., short or long). -/
@[expose] -- for codegen
public def OptHandler (m : Type u → Type v) (α : Type u := PUnit) :=
  (arg : String) → IsOpt arg → m α

/-- Constructs an option handler from a monadic function operating on an arbitrary string. -/
@[inline] public def OptHandler.ofFn (fn : String → m α) : OptHandler m α :=
  fun arg _ => fn arg

/-- Constructs an option handler from a monadic function operating on an string known to be an option. -/
@[inline] public def OptHandler.ofFn' (fn : (arg : String) → IsOpt arg → m α) : OptHandler m α :=
  fn

/-- A monadic callback for a long option (e.g., {lit}`--long` or {lit}`--long=arg`). -/
@[expose] -- for codegen
public def LongOptHandler (m : Type u → Type v) (α : Type u := PUnit) :=
  (opt : String.Slice) → (optArg? : Option String.Slice) → m α

/--
Construct an long option handler from a monadic function that takes the option and its argument.

**Examples:**
* {lit}`-long` => {lean}`fn "-long" none`
* {lit}`--long=arg` => {lean}`fn "--long" (some "arg")`
* {lit}`"--long foo bar"` => {lean}`fn "--long" (some "foo bar")`
-/
@[inline] public def LongOptHandler.ofFn
  (fn : (opt : String.Slice) → (optArg? : Option String.Slice) → m α)
: LongOptHandler m α := fn

/--
Construct an long option handler from a monadic action.

The name of the option (e.g., {lit}`-long` or {lit}`--long`) is available via {name}`getOpt`.
An argument for the option (e.g., {lit}`arg` in {lit}`--long=arg` or {lit}`--long arg`) can be
accessed through {name}`takeArg?`.
-/
@[inline] public def LongOptHandler.ofM (x : OptT m α) : LongOptHandler m α := x

/--
Run the monad with the short option {lean}`opt` of character {lean}`optChar`
with optional argument {lean}`optArg?`.
-/
@[inline] public def ShortOptT.run
  (optChar : Char) (opt : String.Slice) (optArg? : Option String.Slice) (self : ShortOptT m α)
: m α := self optChar opt optArg?

/-- A monadic callback for a short option (e.g., {lit}`-x` or {lit}`-x=arg`). -/
@[expose] -- for codegen
public def ShortOptHandler (m : Type u → Type v) (α : Type u := PUnit) :=
  (optChar : Char) → (opt : String.Slice) → (optArg? : Option String.Slice) → m α

/--
Constructs an short option handler from a monadic function that takes the option and its argument.

**Examples:**
* {lit}`-x` => {lean}`fn 'x' none`
* {lit}`-x=arg` => {lean}`fn 'x' (some "arg")`
* {lit}`"-x foo bar"` => {lean}`fn 'x' (some "foo bar")`
-/
@[inline] public def ShortOptHandler.ofFn
  (fn : (optChar : Char) → (optArg? : Option String.Slice) → m α)
: ShortOptHandler m α := fun c _ a? => fn c a?

/--
Construct an short option handler from a monadic action.

The name of the option (e.g., {lit}`-x`) is available via {name}`getOpt`, and
the character of the option (e.g., {lit}`x` in {lit}`-x`) is available via {name}`getOptChar`,

An argument for the option (e.g., {lit}`arg` in {lit}`-x=arg` or {lit}`-x arg`) can be accessed
through  {name}`takeOptArg`.
-/
@[inline] public def ShortOptHandler.ofM (x : ShortOptT m α) : ShortOptHandler m α := x

/-- A monadic callback for a long short option (e.g., {lit}`-long` or {lit}`-long=short`). -/
@[expose] -- for codegen
public def LongShortOptHandler (m : Type u → Type v) (α : Type u := PUnit) :=
  (arg : String) → IsOpt arg → m α

/-- Constructs a long short option handler from a generic option handler. -/
@[inline] public def LongShortOptHandler.ofOptHandler (handler : OptHandler m α) : LongShortOptHandler m α :=
  handler

public instance : Coe (OptHandler m a) (LongShortOptHandler m a) := ⟨.ofOptHandler⟩

/-- Handlers for each kind of option. -/
public structure OptHandlers (m : Type u → Type v) (α : Type u := PUnit) where
  /-- Process a long option (e.g., {lit}`--long` or {lit}`"--long foo bar"`). -/
  long : LongOptHandler m α
  /-- Process a short option (e.g., {lit}`-x` or {lit}`--`). -/
  short : ShortOptHandler m α
  /-- Process a long short option (e.g., {lit}`-long`, {lit}`-xarg`, or {lit}`-xyz`). -/
  longShort : LongShortOptHandler m α

/-! ## Option Handlers -/

/--
Process a short option of the form {lit}`-xarg`.

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def shortOptionWithArg (handler : ShortOptHandler m α) : OptHandler m α := fun _ h =>
  handler h.shortChar h.shortOpt (some h.shortTail)

/--
Process a multiple short options grouped together
(e.g., {lit}`-xyz` as {lit}`x`, {lit}`y`, {lit}`z`).

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def multiShortOption
  [SeqRight m] (handler : ShortOptHandler m)
: OptHandler m := fun arg h =>
  let rec @[specialize handler] loop (p : arg.Pos) (h : ¬ p.IsAtEnd) :=
    let p' := p.next h
    let optChar := p.get h
    let r := handler optChar s!"-{optChar}" none
    if h' : p'.IsAtEnd then
      r
    else
      r *> loop p' h'
  termination_by p
  loop h.shortPos h.shortPos_ne_endPos

@[inline] private def splitLongOption
  {arg : String} (sepPos : arg.Pos)
  (longHandler : LongOptHandler m α)
  (noSepHandler : ArgHandler m α)
: m α :=
  if h : sepPos = arg.endPos then
    noSepHandler arg
  else
    let optArg := arg.sliceFrom (sepPos.next h)
    let opt := arg.sliceTo sepPos
    longHandler opt (some optArg)

/--
Processes a command line argument as a long option with possible option argument after a ` `
(e.g., {lit}`-long`, {lit}`--long`, or {lit}`"--long arg"`).


Parses a command line argument of the form {lit}`"-opt foo bar"` into the long option
{lit}`-opt` with the option argument {lit}`"foo bar"` and processes it with {lean}`handler`.

If a space is present (e.g., {lit}`-opt foo  bar`), the argument will be split around it.
{lean}`handler` will be invoked with the option {lit}`-opt` and the option argument {lit}`opt`.
Otherwise, the argument is passed to {lean}`handler` as an option with no option argument.

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def longOptionOrSpace (handler : LongOptHandler m α) : OptHandler m α := fun arg _ =>
  splitLongOption (arg.find ' ') handler fun arg => handler arg.toSlice none

/--
Processes a command line argument as a long option with possible option argument after an `=`
(e.g., {lit}`-long`, {lit}`-long`, or {lit}`--long=arg`).

If an equal sign is present (e.g., {lit}`-opt=foo bar`), the argument will be split around it.
{lean}`handler` will be invoked with the option {lit}`-opt` and the option argument {lit}`foo bar`.
Otherwise, the argument is passed to {lean}`handler` as an option with no option argument.

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def longOptionOrEq (handler : LongOptHandler m α) : OptHandler m α := fun arg _ =>
  splitLongOption (arg.find '=') handler fun arg => handler arg.toSlice none

/--
Processes a command line argument as a long option with a possible option argument
(e.g., {lit}`-long`, {lit}`--long`, {lit}`--long=arg`, or {lit}`"--long arg"`).

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] def longOption (handler : LongOptHandler m α) : OptHandler m α := fun arg _ =>
  splitLongOption (arg.find ' ') handler fun arg =>
    splitLongOption (arg.find '=') handler fun arg =>
      handler arg.toSlice none

/-- Processes a short option of the form {lit}`-x`, {lit}`-x=arg`, {lit}`-x arg`, or {lit}`-long`. -/
@[inline] def shortOption
  (shortHandler : ShortOptHandler m α) (longHandler : LongShortOptHandler m α)
: OptHandler m α := fun arg h =>
  if h' : h.afterShortPos.IsAtEnd then -- `-x`
    shortHandler h.shortChar h.shortOpt none
  else -- `-c(.+)`
    let c := h.afterShortPos.get h'
    let nextPos := h.afterShortPos.next h'
    match c with
    | '=' => -- `-x=arg`
      shortHandler h.shortChar h.shortOpt (some <| arg.sliceFrom nextPos)
    | ' ' => -- `"-x arg"`
      shortHandler h.shortChar h.shortOpt (some <| arg.sliceFrom nextPos |>.trimAsciiStart)
    | _   => -- `-long`
      longHandler arg h

/--
Processes an option, short or long, using the given handlers.
An option is an argument of length > 1 starting with a dash ({lit}`-`).
An option may consume additional elements of the argument list.
-/
@[inline] public def option (handlers : OptHandlers m α) : OptHandler m α := fun arg h =>
  if h.shortChar = '-' then -- `--(.*)`
    longOption handlers.long arg h
  else
    shortOption handlers.short handlers.longShort arg h

/-! ## Argument Processors -/

variable [MonadArgs m] [Monad m]

/-- Process the head argument of the list using {lean}`handler` if it is an option. -/
public def processLeadingOption (handler : OptHandler m) : m PUnit := do
  if let arg :: args ← getArgs then
    if h : IsOpt arg then -- `-(.+)`
      setArgs args
      handler arg h

/--
Process the leading options of the remaining argument list.
Consumes empty leading arguments in the argument list.
-/
@[specialize handler]
public partial def processLeadingOptions (handler : OptHandler m) : m PUnit := do
  if let arg :: args ← getArgs then
    if h0 : arg.startPos.IsAtEnd then -- skip empty leading args
      setArgs args
      processLeadingOptions handler
    else if h : arg.startPos.get h0 = '-' ∧ ¬ (arg.startPos.next h0).IsAtEnd then -- `-(.+)`
      setArgs args
      handler arg ⟨h0, h.1, h.2⟩
      processLeadingOptions handler

/-- Process every argument in the command line argument list. -/
@[inline] public partial def processArgs
  (optHandler : OptHandler m) (argHandler : ArgHandler m)
: m PUnit :=
  let rec @[specialize optHandler argHandler] loop := do
    if let some arg ← takeRawArg? then
      if h0 : arg.startPos.IsAtEnd then -- skip empty args
        loop
      else if h : arg.startPos.get h0 = '-' ∧ ¬ (arg.startPos.next h0).IsAtEnd then -- `-(.+)`
        optHandler arg ⟨h0, h.1, h.2⟩
        loop
      else
        argHandler arg
        loop
  loop

/-- Process every option and collect the remaining arguments into an {name}`Array`. -/
@[specialize handler] public partial def collectArgs
  (handler : OptHandler m) (args : Array String := #[])
: m (Array String) := do
  if let some arg ← takeRawArg? then
    if h0 : arg.startPos.IsAtEnd then -- skip empty args
      collectArgs handler args
    else if h : arg.startPos.get h0 = '-' ∧ ¬ (arg.startPos.next h0).IsAtEnd then -- `-(.+)`
      handler arg ⟨h0, h.1, h.2⟩
      collectArgs handler args
    else
      collectArgs handler (args.push arg)
  else
    return args

/-- Process every option in the argument list. -/
@[inline] public def processOptions (handler : OptHandler m) : m PUnit := do
  setArgs (← collectArgs handler).toList

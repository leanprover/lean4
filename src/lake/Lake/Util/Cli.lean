/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.String.Slice
import Init.Data.String.Search
import Init.Data.String.TakeDrop

set_option doc.verso true
set_option linter.missingDocs true

/-! # Lake's CLI API

The abstract API used by Lake to parse command line arguments.
-/

namespace Lake

/-! ## Argument-related Types -/

/-- A command line argument. -/
@[expose] -- for codegen
public def Arg := String

/-- Type class for monads equipped with an command line argument. -/
public abbrev MonadArg (m) := MonadReaderOf Arg m

/-- A List of command line arguments. -/
@[expose] public def ArgList := List String

public noncomputable instance : SizeOf ArgList := inferInstanceAs (SizeOf (List String))

/-- Type class for monads equipped with a command line argument list. -/
public class MonadArgs (m : Type → Type v) where
  /-- Returns the remaining argument list. -/
  getArgs : m (List String)
  /-- Removes and returns the head of the remaining argument list (or {lean}`none` if empty). -/
  takeArg? : m (Option String)
  /-- Removes and returns  the remaining argument list, leaving only an empty list. -/
  takeArgs : m (List String)

export MonadArgs (getArgs takeArgs)

public instance [MonadLift m n] [MonadArgs m] : MonadArgs n where
  getArgs := liftM (m := m) getArgs
  takeArg? := liftM (m := m) MonadArgs.takeArg?
  takeArgs := liftM (m := m) takeArgs

@[always_inline]
public instance  [MonadStateOf ArgList m] : MonadArgs m where
  getArgs := get
  takeArg? := modifyGet fun | [] => (none, []) | arg :: args => (some arg, args)
  takeArgs := modifyGet fun args => (args, [])

/-- A monad transformer to equip a monad with a command-line argument list. -/
@[expose] -- for codegen
public abbrev ArgsT := StateT ArgList

namespace ArgsT

/--
Executes an action in the underlying monad {lean}`m` with the added state of a command-line
argument list. It returns the monadic value paired with the final argument list.
-/
public abbrev run (self : ArgsT m α) (args : List String) : m (α × List String) :=
  StateT.run self args

/--
Executes an action in the underlying monad {lean}`m` with the added state of a command-line
argument list. It returns the monadic value, discarding any remaining arguments list.
-/
public abbrev run' [Functor m] (self : ArgsT m α) (args : List String) : m α :=
  StateT.run' self args

@[simp] public theorem run_getArgs {as : List String} [Monad m]  :
  StateT.run (σ := ArgList) (m := m) getArgs as = pure (as, as)
:= by rfl

@[simp] public theorem run_takeArgs {as : List String} [Monad m] :
  StateT.run (σ := ArgList) (m := m) takeArgs as = pure (as, [])
:= by rfl

end ArgsT

/-- A monad transformer to equip a monad with a state that monotonically non-increasing in size. -/
@[expose] -- for codegen
public def MonoStateT (σ : Type u) [SizeOf σ] (m : Type max u v → Type w) (α : Type v) :=
  (s : σ) → m (α × {s' : σ // sizeOf s' ≤ sizeOf s})

namespace MonoStateT

/-- Construct the monad transformer from its functional definition. -/
@[inline] public def mk
  [SizeOf σ] (fn : (s : σ) → m (α × {s' : σ // sizeOf s' ≤ sizeOf s}))
: MonoStateT σ m α := fn

/--
Executes an action from a monad with added state in the underlying monad {lean}`m`.
Given an initial state {lean}`init : σ`, it returns a value paired with the final state,
which is guaranteed to be a most the size of the initial state.
-/
@[inline] public def run
  [SizeOf σ] (init : σ) (self : MonoStateT σ m α)
: m (α × {s' : σ // sizeOf s' ≤ sizeOf init}) := self init

@[inline, always_inline, inherit_doc Pure.pure]
public protected def pure [SizeOf σ] [Pure m] (a : α) : MonoStateT σ m α :=
  fun args => pure ⟨a, ⟨args, Nat.le_refl _⟩⟩

public instance [SizeOf σ] [Pure m] : Pure (MonoStateT σ m) := ⟨MonoStateT.pure⟩

@[inline, always_inline, inherit_doc Bind.bind]
public protected def bind
  [SizeOf σ] [Monad m] (x : MonoStateT σ m α) (f : α → MonoStateT σ m β)
: MonoStateT σ m β :=
  fun si => bind (x si) fun ⟨a, ⟨sa, ha⟩⟩ => bind (f a sa) fun (b, ⟨sb, hb⟩) =>
    pure ⟨b, ⟨sb, Nat.le_trans hb ha⟩⟩

public instance [SizeOf σ] [Monad m] : Bind (MonoStateT σ m) := ⟨MonoStateT.bind⟩
public instance [SizeOf σ] [Monad m] : Monad (MonoStateT σ m) := {}

/-- Runs an action from the underlying monad in the monad with state. The state is not modified. -/
@[always_inline, inline, expose]
public protected def lift [SizeOf σ] [Monad m] (t : m α) : MonoStateT σ m α :=
  fun s => do let a ← t; pure (a, ⟨s, Nat.le_refl _⟩)

public instance [SizeOf σ] [Monad m] : MonadLift m (MonoStateT σ m) := ⟨MonoStateT.lift⟩

@[always_inline]
public instance [SizeOf σ] [Monad m] [MonadExceptOf ε m] : MonadExceptOf ε (MonoStateT σ m) where
  throw    := MonoStateT.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)

/--
Applies a function to the current state that both computes a new state and
a value. The new state replaces the current state, and the value is returned.
-/
public protected def modifyGet
  [SizeOf σ] [Monad m] (f : (s : σ) → (α × {s' : σ // sizeOf s' ≤ sizeOf s}))
: MonoStateT σ m α := fun s => pure (f s)

/-- Retrieves the current value of the monad's mutable state. -/
@[inline, always_inline]
public protected def get [SizeOf σ] [Pure m] : MonoStateT σ m σ :=
  fun s => pure ⟨s, ⟨s, Nat.le_refl _⟩⟩

end MonoStateT

/-- A monad transformer to equip a monad with a monotonically non-increasing argument list. -/
public abbrev MonoArgsT (m : Type → Type v) := MonoStateT ArgList m

namespace MonoArgsT

@[inline, always_inline, inherit_doc MonadArgs.getArgs]
public protected def get [Pure m] : MonoArgsT m (List String) :=
  MonoStateT.get

@[inline, always_inline, inherit_doc MonadArgs.takeArg?]
public protected def takeArg? [Monad  m] : MonoArgsT m (Option String) :=
  MonoStateT.modifyGet fun
    | [] => (none, ⟨[], Nat.le_refl _⟩)
    | arg :: args => (some arg, ⟨args, mono_cons⟩)
where
  mono_cons {a} {as : List String} : sizeOf as ≤ sizeOf (a :: as) := by simp

@[inline, always_inline, inherit_doc MonadArgs.takeArgs]
public protected def takeArgs [Monad  m] : MonoArgsT m (List String) :=
   MonoStateT.modifyGet fun args => (args, ⟨[], mono_nil⟩)
where
  mono_nil {as : List String} : sizeOf ([] : List String) ≤ sizeOf as := by
    cases as
    · simp
    · simp only [List.nil.sizeOf_spec, List.cons.sizeOf_spec]
      omega

public instance [Monad m] : MonadArgs (MonoArgsT m) where
  getArgs := MonoArgsT.get
  takeArg? := MonoArgsT.takeArg?
  takeArgs :=  MonoArgsT.takeArgs

end MonoArgsT

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
  if let some arg ← MonadArgs.takeArg? then
    return some (← parseArg arg)
  else
    return none

@[simp] public theorem ArgsT.run_takeArg?_nil
  [Monad m] [LawfulMonad m] {_ : MonadParseArg α (ArgsT m)} :
  StateT.run (σ := ArgList) (m := m) takeArg? [] = pure ((none : Option α), [])
:= by simp [takeArg?, MonadArgs.takeArg?]

@[simp] public theorem ArgsT.run_takeArg?_cons
  [Monad m] [LawfulMonad m] [MonadParseArg α (ArgsT m)] :
  StateT.run (σ := ArgList) (m := m) (α := Option α) takeArg? (a :: as) =
  StateT.run (σ := ArgList) (some <$> parseArg a) as
:= by simp [takeArg?, MonadArgs.takeArg?]

/--
Removes and returns the head of the remaining argument list, parsing the argument into {lean}`α`.

If no argument is available, returns {lean}`default`.
-/
@[inline] public def takeArgD
  [Monad m] [MonadArgs m] [MonadParseArg α m] (default : α)
: m α := return (← takeArg?).getD default

@[simp] public theorem takeArgD_eq_getD_takeArg?
  [Monad m] [LawfulMonad m] [MonadArgs m] [MonadParseArg α m] :
  takeArgD (α := α) (m := m) d = (·.getD d) <$> takeArg?
:= by simp [takeArgD]

/--
Removes and returns the head of the remaining argument list, parsing the argument into {lean}`α`.

If no argument is available,, errors using {name}`throwExpectedArg` with {lean}`descr`.
-/
@[inline] public def takeArg
  [Monad m] [MonadArgs m] [MonadParseArg α m] [MonadThrowExpectedArg m] (descr : String)
: m α := do
  if let some arg ← MonadArgs.takeArg? then
    parseArg arg
  else
    throwExpectedArg descr

@[simp] public theorem ArgsT.run_takeArg_nil
  [Monad m] [LawfulMonad m] [MonadParseArg α (ArgsT m)] [MonadThrowExpectedArg m] :
  StateT.run (σ := ArgList) (m := m) (α := α) (takeArg d) [] =
  ((·, [])) <$> throwExpectedArg (m := m) d
:= by simp [takeArg, MonadArgs.takeArg?, throwExpectedArg]

@[simp] public theorem ArgsT.run_takeArg_cons
  [Monad m] [LawfulMonad m] [MonadParseArg α (ArgsT m)] {_ : MonadThrowExpectedArg m} :
  StateT.run (σ := ArgList) (m := m) (α := α) (takeArg d) (a :: as) =
  StateT.run (σ := ArgList) (parseArg a) as
:= by simp [takeArg, MonadArgs.takeArg?]

/-! ## Argument Handler Type -/

/-- A monadic callback for an arbitrary command line argument. -/
@[expose] -- for codegen
public def ArgHandler (m : Type → Type v) :=
  (arg : String) → (args : List String) → m {remArgs : List String // sizeOf remArgs ≤ sizeOf args}

/-- Get the current command line argument of the context (e.g., in an {name}`ArgHandler`). -/
@[inline] public def getArg [MonadArg m] : m String :=
  read

/-- A monad transformer to equip a monad with a command line argument. -/
public abbrev ArgT (m) := ReaderT Arg <| MonoArgsT m

/--
Construct an argument handler from a monadic action.

The argument under analysis is available via {name}`getArg`. Further arguments are available
through {name}`getArgs` and can be modify through the various {name}`MonadArgs` utilities
(e.g., {name}`takeArg`).
-/
@[inline] public def ArgHandler.ofM [Monad m] (x : ArgT m Unit) : ArgHandler m :=
  fun arg args => (·.2) <$> x arg args

/-! ## Argument Predicates -/

/--
{lean}`IsOpt arg` holds if {lean}`arg` is an command line option.
That is, {lean}`arg` is of the form `-(.+)`.
-/
public structure IsOpt (arg : String) : Prop where
  startPos_ne_endPos : arg.startPos ≠ arg.endPos
  get_startPos : arg.startPos.get startPos_ne_endPos = '-'
  next_startPos_ne_endPos : arg.startPos.next startPos_ne_endPos ≠ arg.endPos

/--
{lean}`IsArg arg` holds if {lean}`arg` is a non-option command-line argument
That is, it is not empty and is not of the form `-(.+)`.
-/
public structure IsArg (arg : String) : Prop where
  ne_empty : arg ≠ ""
  not_isOpt : ¬ IsOpt arg

namespace IsOpt

/-- A decision procedure for determining if {lean}`arg` is an option. -/
@[reducible, expose] public def dec (arg : String) : Decidable (IsOpt arg) :=
  if h0 : arg.startPos = arg.endPos then
    isFalse fun ⟨_, _, _⟩ => by contradiction
  else
    if hc : arg.startPos.get h0 = '-' then
      if h1 : arg.startPos.next h0 = arg.endPos then
        isFalse fun ⟨_, _, _⟩ => by contradiction
      else
        isTrue ⟨h0, hc, h1⟩
    else
      isFalse fun ⟨_, _, _⟩ => by contradiction

public instance instDecidable {arg : String} : Decidable (IsOpt arg) := dec arg

public theorem ne_empty {arg} (h : IsOpt arg) : arg ≠ "" :=
  String.startPos_eq_endPos_iff.subst h.startPos_ne_endPos

public theorem not_isArg {arg} (h : IsOpt arg) : ¬ IsArg arg :=
  fun h' => h'.not_isOpt h

public theorem ne_of_isArg (ha : IsOpt a) (hb : IsArg b) : a ≠ b :=
  fun heq => ha.not_isArg.elim (heq ▸ hb)

public theorem offset_next_startPos (h : IsOpt a) :
  (a.startPos.next h.startPos_ne_endPos).offset = ⟨1⟩
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

namespace IsArg

/-- A decision procedure for determining if {lean}`arg` is an non-option command line argument. -/
@[reducible, expose] public def dec (arg : String) : Decidable (IsArg arg) :=
  if h0 : arg.startPos = arg.endPos then
    isFalse fun h => h.ne_empty (String.startPos_eq_endPos_iff.mp h0)
  else
    have ne_empty := String.startPos_eq_endPos_iff.subst h0
    if hc : arg.startPos.get h0 = '-' then
      if h1 : arg.startPos.next h0 = arg.endPos then
        isTrue ⟨ne_empty, fun h => h.next_startPos_ne_endPos h1⟩
      else
        isFalse fun h => h.not_isOpt ⟨h0, hc, h1⟩
    else
      isTrue ⟨ne_empty, fun h => hc h.get_startPos⟩

public instance instDecidable {arg : String} : Decidable (IsArg arg) := dec arg

public theorem ne_of_isOpt (ha : IsArg a) (hb : IsOpt b) : a ≠ b :=
  fun heq => ha.not_isOpt.elim (heq ▸ hb)

public theorem startPos_ne_endPos (h : IsArg a) : a.startPos ≠ a.endPos :=
  String.startPos_eq_endPos_iff.symm.subst h.ne_empty

theorem startPos_wf (h : IsArg a) :
  ¬ (a.startPos.get h.startPos_ne_endPos = '-' ∧ ¬ a.startPos.next h.startPos_ne_endPos = a.endPos)
:= by
  intro h'
  refine h.not_isOpt.elim ⟨?_, h'.1, h'.2⟩
  simpa using h.ne_empty

end IsArg

/-! ## Option-related Types -/

/-- A command line option. -/
@[expose] -- for codegen
public def Opt := String.Slice

/-- Type class for monads equipped with an command line option. -/
public abbrev MonadOpt (m) := MonadReaderOf Opt m

/-- An optional command line option argument. -/
@[expose] -- for codegen
public def OptArg := Option String.Slice

/-- Type class for monads equipped with an optional command line option argument. -/
public abbrev MonadOptArg (m) := MonadReaderOf OptArg m

/-- A monad transformer to equip a monad with a command line option and optional argument. -/
public abbrev OptT (m) := ReaderT Opt <| ReaderT OptArg <| MonoArgsT m

/-- The character of a command line short option (e.g., {lit}`x` of {lit}`-x`). -/
@[expose] -- for codegen
public def OptChar := Char

/-- Type class for monads equipped with a command line short option. -/
public abbrev MonadOptChar (m) := MonadReaderOf OptChar m

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
public def OptHandler (m : Type → Type v) :=
  (arg : String) → IsOpt arg →
  (args : List String) → m {remArgs : List String // sizeOf remArgs ≤ sizeOf args}

/-- A monad transformer to equip a monad with a long option and optional argument. -/
public abbrev LongOptT (m) := OptT m

/-- A monadic callback for a long option (e.g., {lit}`--long` or {lit}`--long=arg`). -/
@[expose] -- for codegen
public def LongOptHandler (m : Type → Type v) :=
  (opt : String.Slice) → (optArg? : Option String.Slice) →
  (args : List String) → m {remArgs : List String // sizeOf remArgs ≤ sizeOf args}

/--
Construct an long option handler from a monadic action.

The name of the option (e.g., {lit}`-long` or {lit}`--long`) is available via {name}`getOpt`.
An argument for the option (e.g., {lit}`arg` in {lit}`--long=arg` or {lit}`--long arg`) can be
accessed through {name}`takeArg?`.
-/
@[inline] public def LongOptHandler.ofM [Monad m] (x : LongOptT m Unit) : LongOptHandler m :=
  fun opt optArg? args => (·.2) <$> x opt optArg? args

/-- A monadic callback for a short option (e.g., {lit}`-x` or {lit}`-x=arg`). -/
@[expose] -- for codegen
public def ShortOptHandler (m : Type → Type v) :=
  (optChar : Char) → (opt : String.Slice) → (optArg? : Option String.Slice) →
  (args : List String) → m {remArgs : List String // sizeOf remArgs ≤ sizeOf args}

/-- A monad transformer to equip a monad with a short option and optional argument. -/
public abbrev ShortOptT (m) := ReaderT OptChar <| OptT m

/--
Construct an short option handler from a monadic action.

The name of the option (e.g., {lit}`-x`) is available via {name}`getOpt`, and
the character of the option (e.g., {lit}`x` in {lit}`-x`) is available via {name}`getOptChar`,

An argument for the option (e.g., {lit}`arg` in {lit}`-x=arg` or {lit}`-x arg`) can be accessed
through  {name}`takeOptArg`.
-/
@[inline] public def ShortOptHandler.ofM [Monad m] (x : ShortOptT m Unit) : ShortOptHandler m :=
  fun optChar opt optArg? args => (·.2) <$> x optChar opt optArg? args

/-- A monadic callback for a long short option (e.g., {lit}`-long` or {lit}`-long=short`). -/
@[expose] -- for codegen
public def LongShortOptHandler (m : Type → Type v)  :=
  OptHandler m

/-- Constructs a long short option handler from a generic option handler. -/
@[inline] public def LongShortOptHandler.ofOptHandler (handler : OptHandler m) : LongShortOptHandler m :=
  handler

public instance : Coe (OptHandler m) (LongShortOptHandler m) := ⟨.ofOptHandler⟩

/-- Handlers for each kind of option. -/
public structure OptHandlers (m : Type → Type v) where
  /-- Process a long option (e.g., {lit}`--long` or {lit}`"--long foo bar"`). -/
  long : LongOptHandler m
  /-- Process a short option (e.g., {lit}`-x` or {lit}`--`). -/
  short : ShortOptHandler m
  /-- Process a long short option (e.g., {lit}`-long`, {lit}`-xarg`, or {lit}`-xyz`). -/
  longShort : LongShortOptHandler m

/-! ## Option Handlers -/

/--
Process a short option of the form {lit}`-xarg`.

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def shortOptionWithArg (handler : ShortOptHandler m) : OptHandler m := fun _ h =>
  handler h.shortChar h.shortOpt (some h.shortTail)

/--
Process a multiple short options grouped together
(e.g., {lit}`-xyz` as {lit}`x`, {lit}`y`, {lit}`z`).

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def multiShortOption
  [SeqRight m] (handler : ShortOptHandler m)
: OptHandler m := fun arg h args =>
  let rec @[specialize handler] loop (p : arg.Pos) (h : ¬ p.IsAtEnd) :=
    let p' := p.next h
    let optChar := p.get h
    let r := handler optChar s!"-{optChar}" none args
    if h' : p'.IsAtEnd then
      r
    else
      r *> loop p' h'
  termination_by p
  loop h.shortPos h.shortPos_ne_endPos

@[inline] private def splitLongOption
  {arg : String} (sepPos : arg.Pos) (args : List String)
  (longHandler : LongOptHandler m)
  (noSepHandler : ArgHandler m)
: m {remArgs : List String // sizeOf remArgs ≤ sizeOf args} :=
  if h : sepPos = arg.endPos then
    noSepHandler arg args
  else
    let optArg := arg.sliceFrom (sepPos.next h)
    let opt := arg.sliceTo sepPos
    longHandler opt (some optArg) args

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
@[inline] public def longOptionOrSpace (handler : LongOptHandler m) : OptHandler m := fun arg _ args =>
  splitLongOption (arg.find ' ') args handler fun arg => handler arg.toSlice none

/--
Processes a command line argument as a long option with possible option argument after an `=`
(e.g., {lit}`-long`, {lit}`-long`, or {lit}`--long=arg`).

If an equal sign is present (e.g., {lit}`-opt=foo bar`), the argument will be split around it.
{lean}`handler` will be invoked with the option {lit}`-opt` and the option argument {lit}`foo bar`.
Otherwise, the argument is passed to {lean}`handler` as an option with no option argument.

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] public def longOptionOrEq (handler : LongOptHandler m) : OptHandler m := fun arg _ args =>
  splitLongOption (arg.find '=') args handler fun arg => handler arg.toSlice none

/--
Processes a command line argument as a long option with a possible option argument
(e.g., {lit}`-long`, {lit}`--long`, {lit}`--long=arg`, or {lit}`"--long arg"`).

Can be used as the handler for {lean}`OptHandlers.longShort`.
-/
@[inline] def longOption (handler : LongOptHandler m) : OptHandler m := fun arg _ args =>
  splitLongOption (arg.find ' ') args handler fun arg args =>
    splitLongOption (arg.find '=') args handler fun arg =>
      handler arg.toSlice none

/-- Processes a short option of the form {lit}`-x`, {lit}`-x=arg`, {lit}`-x arg`, or {lit}`-long`. -/
@[inline] def shortOption
  (shortHandler : ShortOptHandler m) (longHandler : LongShortOptHandler m)
: OptHandler m := fun arg h =>
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
@[inline] public def option (handlers : OptHandlers m) : OptHandler m := fun arg h =>
  if h.shortChar = '-' then -- `--(.*)`
    longOption handlers.long arg h
  else
    shortOption handlers.short handlers.longShort arg h

/-! ## Argument Processors -/

/-- Process the head argument of the list using {lean}`handler` if it is an option. -/
@[inline] public def processLeadingOption
  [Monad m] (args : List String) (handler : OptHandler m)
: m (List String) :=
  if let arg :: remArgs := args then
    if h : IsOpt arg then -- `-(.+)`
      handler arg h remArgs
    else
      pure args
  else
    pure args

/--
Process the leading options of the remaining argument list.
Consumes empty leading arguments in the argument list.
-/
@[specialize handler]
public def processLeadingOptions
  [Monad m] (args : List String) (handler : OptHandler m)
: m (List String) := do
  if let a :: as := args then
    if h0 : a.startPos.IsAtEnd then -- skip empty leading args
      processLeadingOptions as handler
    else if h : a.startPos.get h0 = '-' ∧ ¬ (a.startPos.next h0).IsAtEnd then -- `-(.+)`
      let ⟨as, _⟩ ← handler a ⟨h0, h.1, h.2⟩ as
      processLeadingOptions as handler
    else
      return args
  else
    return args
termination_by args

@[simp] public theorem processLeadingOptions_nil [Monad m] :
  processLeadingOptions (m := m) [] f = pure []
:= by unfold processLeadingOptions; simp

@[simp] public theorem processLeadingOptions_cons_empty [Monad m] :
  processLeadingOptions (m := m) ("" :: as) f = processLeadingOptions as f
:= by conv => {lhs; unfold processLeadingOptions}; simp

public theorem processLeadingOptions_cons_of_isOpt [Monad m] (h : IsOpt a) :
  processLeadingOptions (m := m) (a :: as) f =
    f a h as >>= fun as => processLeadingOptions as f
:= by
  conv => lhs; unfold processLeadingOptions
  simp [h.ne_empty, h.get_startPos, h.next_startPos_ne_endPos]

public theorem processLeadingOptions_cons_of_isArg [Monad m] (h : IsArg a) :
  processLeadingOptions (m := m) (a :: as) f = pure (a :: as)
:= by
  conv => lhs; unfold processLeadingOptions
  simp [h.ne_empty, h.startPos_wf]

/-- Process every argument in the command line argument list. -/
@[inline] public def processArgs
  [Monad m] (args : List String) (optHandler : OptHandler m) (argHandler : ArgHandler m)
: m PUnit :=
  let rec @[specialize optHandler argHandler] loop args := do
    if let a :: as := args then
      if h0 : a.startPos.IsAtEnd then -- skip empty args
        loop as
      else if h : a.startPos.get h0 = '-' ∧ ¬ (a.startPos.next h0).IsAtEnd then -- `-(.+)`
        let ⟨as, _⟩ ← optHandler a ⟨h0, h.1, h.2⟩ as
        loop as
      else
        let ⟨as, _⟩ ← argHandler a as
        loop as
  termination_by args
  loop args

@[simp] public theorem processArgs_nil [Monad m] :
  processArgs (m := m) [] optH argH = pure ()
:= by unfold processArgs processArgs.loop; simp

@[simp] public theorem processArgs_cons_empty [Monad m] :
  processArgs (m := m) ("" :: as) optH argH = processArgs as optH argH
:= by
  unfold processArgs
  conv => lhs; unfold processArgs.loop
  simp

public theorem processArgs_cons_of_isOpt [Monad m] (h : IsOpt a) :
  processArgs (m := m) (a :: as) optH argH =
    optH a h as >>= fun as => processArgs as optH argH
:= by
  unfold processArgs
  conv => lhs; unfold processArgs.loop
  simp [h.ne_empty, h.get_startPos, h.next_startPos_ne_endPos]

public theorem processArgs_cons_of_isArg [Monad m] (h : IsArg a) :
  processArgs (m := m) (a :: as) optH argH =
    argH a as >>= fun as => processArgs as optH argH
:= by
  unfold processArgs
  conv => lhs; unfold processArgs.loop
  simp [h.ne_empty, h.startPos_wf]

@[inline] def OptHandler.lift [MonadLift m n] (self : OptHandler m) : OptHandler n :=
  fun arg h args => liftM (self arg h args)

/-- Process every option in {lean}`args` and collect the remaining arguments into an {name}`Array`. -/
@[inline] public def collectArgs
  [Monad m] (args : List String) (handler : OptHandler m)
: m (Array String) :=
  (·.2) <$> StateT.run (s := #[]) do
    processArgs args handler.lift fun arg args s =>
      pure (⟨args, Nat.le_refl ..⟩, s.push arg)

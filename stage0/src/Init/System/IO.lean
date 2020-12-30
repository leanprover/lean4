/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.EState
import Init.Control.Reader
import Init.Data.String
import Init.Data.ByteArray
import Init.System.IOError
import Init.System.FilePath
import Init.System.ST
import Init.Data.ToString.Macro

/-- Like https://hackage.haskell.org/package/ghc-Prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `IO` operations.

    TODO: mark opaque -/
def IO.RealWorld : Type := Unit

/- TODO(Leo): mark it as an opaque definition. Reason: prevent
   functions defined in other modules from accessing `IO.RealWorld`.
   We don't want action such as
   ```
   def getWorld : IO (IO.RealWorld) := get
   ```
-/
def EIO (ε : Type) : Type → Type := EStateM ε IO.RealWorld

@[inline] def EIO.catchExceptions (x : EIO ε α) (h : ε → EIO Empty α) : EIO Empty α :=
  fun s => match x s with
  | EStateM.Result.ok a s     => EStateM.Result.ok a s
  | EStateM.Result.error ex s => h ex s

instance : Monad (EIO ε) := inferInstanceAs (Monad (EStateM ε IO.RealWorld))
instance : MonadFinally (EIO ε) := inferInstanceAs (MonadFinally (EStateM ε IO.RealWorld))
instance : MonadExceptOf ε (EIO ε) := inferInstanceAs (MonadExceptOf ε (EStateM ε IO.RealWorld))
instance : OrElse (EIO ε α) := ⟨MonadExcept.orelse⟩
instance [Inhabited ε] : Inhabited (EIO ε α) := inferInstanceAs (Inhabited (EStateM ε IO.RealWorld α))

open IO (Error) in
abbrev IO : Type → Type := EIO Error

@[inline] def EIO.toIO (f : ε → IO.Error) (x : EIO ε α) : IO α :=
  x.adaptExcept f

@[inline] def EIO.toIO' (x : EIO ε α) : IO (Except ε α) :=
  EIO.toIO (fun _ => unreachable!) (observing x)

@[inline] def IO.toEIO (f : IO.Error → ε) (x : IO α) : EIO ε α :=
  x.adaptExcept f

/- After we inline `EState.run'`, the closed term `((), ())` is generated, where the second `()`
   represents the "initial world". We don't want to cache this closed term. So, we disable
   the "extract closed terms" optimization. -/
set_option compiler.extract_closed false in
@[inline] unsafe def unsafeEIO (fn : EIO ε α) : Except ε α :=
  match fn.run () with
  | EStateM.Result.ok a _    => Except.ok a
  | EStateM.Result.error e _ => Except.error e

@[inline] unsafe def unsafeIO (fn : IO α) : Except IO.Error α :=
  unsafeEIO fn

@[extern "lean_io_timeit"] constant timeit (msg : @& String) (fn : IO α) : IO α
@[extern "lean_io_allocprof"] constant allocprof (msg : @& String) (fn : IO α) : IO α

/- Programs can execute IO actions during initialization that occurs before
   the `main` function is executed. The attribute `[init <action>]` specifies
   which IO action is executed to set the value of an opaque constant.

   The action `initializing` returns `true` iff it is invoked during initialization. -/
@[extern "lean_io_initializing"] constant IO.initializing : IO Bool

namespace IO

def ofExcept [ToString ε] (e : Except ε α) : IO α :=
  match e with
  | Except.ok a    => pure a
  | Except.error e => throw (IO.userError (toString e))

def lazyPure (fn : Unit → α) : IO α :=
  pure (fn ())


def sleep (ms : UInt32) : IO Unit :=
  -- TODO: add a proper primitive for IO.sleep
  fun s => dbgSleep ms fun _ => EStateM.Result.ok () s

/--
  Run `act` in a separate `Task`. This is similar to Haskell's [`unsafeInterleaveIO`](http://hackage.haskell.org/package/base-4.14.0.0/docs/System-IO-Unsafe.html#v:unsafeInterleaveIO),
  except that the `Task` is started eagerly as usual. Thus pure accesses to the `Task` do not influence the impure `act`
  computation.
  Unlike with pure tasks created by `Task.mk`, tasks created by this function will be run even if the last reference
  to the task is dropped. `act` should manually check for cancellation via `IO.checkCanceled` if it wants to react
  to that. -/
@[extern "lean_io_as_task"]
constant asTask (act : IO α) (prio := Task.Priority.default) : IO (Task (Except IO.Error α))

/-- See `IO.asTask`. -/
@[extern "lean_io_map_task"]
constant mapTask (f : α → IO β) (t : Task α) (prio := Task.Priority.default) : IO (Task (Except IO.Error β))

/-- See `IO.asTask`. -/
@[extern "lean_io_bind_task"]
constant bindTask (t : Task α) (f : α → IO (Task (Except IO.Error β))) (prio := Task.Priority.default) : IO (Task (Except IO.Error β))

/-- Check if the task's cancellation flag has been set by calling `IO.cancel` or dropping the last reference to the task. -/
@[extern "lean_io_check_canceled"] constant checkCanceled : IO Bool

/-- Request cooperative cancellation of the task. The task must explicitly call `IO.checkCanceled` to react to the cancellation. -/
@[extern "lean_io_cancel"] constant cancel : @& Task α → IO Unit

/-- Check if the task has finished execution, at which point calling `Task.get` will return immediately. -/
@[extern "lean_io_has_finished"] constant hasFinished : @& Task α → IO Bool

/-- Wait for the task to finish, then return its result. -/
@[extern "lean_io_wait"] constant wait : Task α → IO α

/-- Wait until any of the tasks in the given list has finished, then return its result. -/
@[extern "lean_io_wait_any"] constant waitAny : @& List (Task α) → IO α

inductive FS.Mode where
  | read | write | readWrite | append

constant FS.Handle : Type := Unit

/--
  A pure-Lean abstraction of POSIX streams. We use `Stream`s for the standard streams stdin/stdout/stderr so we can
  capture output of `#eval` commands into memory. -/
structure FS.Stream where
  isEof   : IO Bool
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit

namespace Prim
open FS

@[extern "lean_get_stdin"] constant getStdin  : IO FS.Stream
@[extern "lean_get_stdout"] constant getStdout : IO FS.Stream
@[extern "lean_get_stderr"] constant getStderr : IO FS.Stream

@[extern "lean_get_set_stdin"] constant setStdin  : FS.Stream → IO FS.Stream
@[extern "lean_get_set_stdout"] constant setStdout : FS.Stream → IO FS.Stream
@[extern "lean_get_set_stderr"] constant setStderr : FS.Stream → IO FS.Stream

@[specialize] partial def iterate (a : α) (f : α → IO (Sum α β)) : IO β := do
  let v ← f a
  match v with
  | Sum.inl a => iterate a f
  | Sum.inr b => pure b

-- @[export lean_fopen_flags]
def fopenFlags (m : FS.Mode) (b : Bool) : String :=
  let mode :=
    match m with
    | FS.Mode.read      => "r"
    | FS.Mode.write     => "w"
    | FS.Mode.readWrite => "r+"
    | FS.Mode.append    => "a" ;
  let bin := if b then "b" else "t"
  mode ++ bin

@[extern "lean_io_prim_handle_mk"] constant Handle.mk (s : @& String) (mode : @& String) : IO Handle
@[extern "lean_io_prim_handle_size"] constant Handle.size (h : @& Handle) : IO Nat
@[extern "lean_io_prim_handle_is_eof"] constant Handle.isEof (h : @& Handle) : IO Bool
@[extern "lean_io_prim_handle_flush"] constant Handle.flush (h : @& Handle) : IO Unit
@[extern "lean_io_prim_handle_read"] constant Handle.read  (h : @& Handle) (bytes : USize) : IO ByteArray
@[extern "lean_io_prim_handle_write"] constant Handle.write (h : @& Handle) (buffer : @& ByteArray) : IO Unit

@[extern "lean_io_prim_handle_get_line"] constant Handle.getLine (h : @& Handle) : IO String
@[extern "lean_io_prim_handle_put_str"] constant Handle.putStr (h : @& Handle) (s : @& String) : IO Unit

@[extern "lean_io_getenv"] constant getEnv (var : @& String) : IO (Option String)
@[extern "lean_io_realpath"] constant realPath (fname : String) : IO String
@[extern "lean_io_is_dir"] constant isDir (fname : @& String) : IO Bool
@[extern "lean_io_file_exists"] constant fileExists (fname : @& String) : IO Bool
@[extern "lean_io_app_dir"] constant appPath : IO String
@[extern "lean_io_current_dir"] constant currentDir : IO String

end Prim

namespace FS
variables [Monad m] [MonadLiftT IO m]

def Handle.mk (s : String) (Mode : Mode) (bin : Bool := true) : m Handle :=
  liftM (Prim.Handle.mk s (Prim.fopenFlags Mode bin))

@[inline]
def withFile (fn : String) (mode : Mode) (f : Handle → m α) : m α :=
  Handle.mk fn mode >>= f

/-- Returns the size of the underlying file. -/
def Handle.size : Handle → m Nat := liftM ∘ Prim.Handle.size
/-- returns whether the end of the file has been reached while reading a file.
`h.isEof` returns true /after/ the first attempt at reading past the end of `h`.
Once `h.isEof` is true, the reading `h` raises `IO.Error.eof`.
-/
def Handle.isEof : Handle → m Bool := liftM ∘ Prim.Handle.isEof
def Handle.flush : Handle → m Unit := liftM ∘ Prim.Handle.flush
def Handle.read (h : Handle) (bytes : Nat) : m ByteArray := liftM (Prim.Handle.read h (USize.ofNat bytes))
def Handle.write (h : Handle) (s : ByteArray) : m Unit := liftM (Prim.Handle.write h s)

def Handle.getLine : Handle → m String := liftM ∘ Prim.Handle.getLine

def Handle.putStr (h : Handle) (s : String) : m Unit :=
  liftM <| Prim.Handle.putStr h s

def Handle.putStrLn (h : Handle) (s : String) : m Unit :=
  h.putStr (s.push '\n')

partial def Handle.readBinToEnd (h : Handle) : m ByteArray := do
  let rec loop (left : Nat) : m ByteArray := do
    if left == 0 then ByteArray.empty
    else
      let buf ← h.read left
      let left := left - buf.size
      pure $ buf ++ (←loop left)
  loop (←h.size)

partial def Handle.readToEnd (h : Handle) : m String := do
  let rec read (s : String) := do
    let line ← h.getLine
    if line.length == 0 then pure s else read (s ++ line)
  read ""

def readBinFile (fname : String) : m ByteArray := do
  let h ← Handle.mk fname Mode.read true
  h.readBinToEnd

def readFile (fname : String) : m String := do
  let h ← Handle.mk fname Mode.read false
  h.readToEnd

partial def lines (fname : String) : m (Array String) := do
  let h ← Handle.mk fname Mode.read false
  let rec read (lines : Array String) := do
    let line ← h.getLine
    if line.length == 0 then
      pure lines
    else if line.back == '\n' then
      let line := line.dropRight 1
      let line := if System.Platform.isWindows && line.back == '\x0d' then line.dropRight 1 else line
      read <| lines.push line
    else
      pure <| lines.push line
  read #[]

def writeBinFile (fname : String) (content : ByteArray) : m Unit := do
  let h ← Handle.mk fname Mode.write true
  h.write content

def writeFile (fname : String) (content : String) : m Unit := do
  let h ← Handle.mk fname Mode.write false
  h.putStr content

namespace Stream

def putStrLn (strm : FS.Stream) (s : String) : m Unit :=
  liftM (strm.putStr (s.push '\n'))

end Stream

end FS

section
variables [Monad m] [MonadLiftT IO m]

def getStdin : m FS.Stream := liftM Prim.getStdin
def getStdout : m FS.Stream := liftM Prim.getStdout
def getStderr : m FS.Stream := liftM Prim.getStderr

/-- Replaces the stdin stream of the current thread and returns its previous value. -/
def setStdin : FS.Stream → m FS.Stream := liftM ∘ Prim.setStdin

/-- Replaces the stdout stream of the current thread and returns its previous value. -/
def setStdout : FS.Stream → m FS.Stream := liftM ∘ Prim.setStdout

/-- Replaces the stderr stream of the current thread and returns its previous value. -/
def setStderr : FS.Stream → m FS.Stream := liftM ∘ Prim.setStderr

def withStdin [MonadFinally m] (h : FS.Stream) (x : m α) : m α := do
  let prev ← setStdin h
  try x finally discard <| setStdin prev

def withStdout [MonadFinally m] (h : FS.Stream) (x : m α) : m α := do
  let prev ← setStdout h
  try
    x
  finally
    discard <| setStdout prev

def withStderr [MonadFinally m] (h : FS.Stream) (x : m α) : m α := do
  let prev ← setStderr h
  try x finally discard <| setStderr prev

def print [ToString α] (s : α) : IO Unit := do
  let out ← getStdout
  out.putStr <| toString s

def println [ToString α] (s : α) : IO Unit :=
  print ((toString s).push '\n')

def eprint [ToString α] (s : α) : IO Unit := do
  let out ← getStderr
  liftM <| out.putStr <| toString s

def eprintln [ToString α] (s : α) : IO Unit :=
  eprint <| toString s |>.push '\n'

@[export lean_io_eprintln]
private def eprintlnAux (s : String) : IO Unit :=
  eprintln s

def getEnv : String → m (Option String) := liftM ∘ Prim.getEnv
def realPath : String → m String := liftM ∘ Prim.realPath
def isDir : String → m Bool := liftM ∘ Prim.isDir
def fileExists : String → m Bool := liftM ∘ Prim.fileExists
def appPath : m String := liftM Prim.appPath

def appDir : m String := do
  let p ← appPath
  realPath (System.FilePath.dirName p)

def currentDir : m String := liftM Prim.currentDir

end

namespace Process
inductive Stdio where
  | piped
  | inherit
  | null

def Stdio.toHandleType : Stdio → Type
  | Stdio.piped   => FS.Handle
  | Stdio.inherit => Unit
  | Stdio.null    => Unit

structure StdioConfig where
  /- Configuration for the process' stdin handle. -/
  stdin := Stdio.inherit
  /- Configuration for the process' stdout handle. -/
  stdout := Stdio.inherit
  /- Configuration for the process' stderr handle. -/
  stderr := Stdio.inherit

structure SpawnArgs extends StdioConfig where
  /- Command name. -/
  cmd : String
  /- Arguments for the process -/
  args : Array String := #[]
  /- Working directory for the process. Inherit from current process if `none`. -/
  cwd : Option String := none
  /- Add or remove environment variables for the process. -/
  env : Array (String × Option String) := #[]

-- TODO(Sebastian): constructor must be private
structure Child (cfg : StdioConfig) where
  stdin  : cfg.stdin.toHandleType
  stdout : cfg.stdout.toHandleType
  stderr : cfg.stderr.toHandleType

@[extern "lean_io_process_spawn"] constant spawn (args : SpawnArgs) : IO (Child args.toStdioConfig)

@[extern "lean_io_process_child_wait"] constant Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32

structure Output where
  exitCode : UInt32
  stdout   : String
  stderr   : String

/-- Run process to completion and capture output. -/
def output (args : SpawnArgs) : IO Output := do
  let child ← spawn { args with stdout := Stdio.piped, stderr := Stdio.piped }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  pure { exitCode := exitCode, stdout := stdout, stderr := stderr }

/-- Run process to completion and return stdout on success. -/
def run (args : SpawnArgs) : IO String := do
  let out ← output args
  if out.exitCode != 0 then
    throw <| IO.userError <| "process '" ++ args.cmd ++ "' exited with code " ++ toString out.exitCode;
  pure out.stdout

end Process

structure AccessRight where
  read : Bool := false
  write : Bool := false
  execution : Bool := false

def AccessRight.flags (acc : AccessRight) : UInt32 :=
  let r : UInt32 := if acc.read      then 0x4 else 0
  let w : UInt32 := if acc.write     then 0x2 else 0
  let x : UInt32 := if acc.execution then 0x1 else 0
  r.lor <| w.lor x

structure FileRight where
  user  : AccessRight := {}
  group : AccessRight := {}
  other : AccessRight := {}

def FileRight.flags (acc : FileRight) : UInt32 :=
  let u : UInt32 := acc.user.flags.shiftLeft 6
  let g : UInt32 := acc.group.flags.shiftLeft 3
  let o : UInt32 := acc.other.flags
  u.lor <| g.lor o

@[extern "lean_chmod"] constant Prim.setAccessRights (filename : @& String) (mode : UInt32) : IO Unit

def setAccessRights (filename : String) (mode : FileRight) : IO Unit :=
  Prim.setAccessRights filename mode.flags

/- References -/
abbrev Ref (α : Type) := ST.Ref IO.RealWorld α

instance : MonadLift (ST IO.RealWorld) (EIO ε) := ⟨fun x s =>
  match x s with
  | EStateM.Result.ok a s     => EStateM.Result.ok a s
  | EStateM.Result.error ex _ => nomatch ex⟩

def mkRef [Monad m] [MonadLiftT (ST IO.RealWorld) m] (a : α) : m (IO.Ref α) :=
  ST.mkRef a

namespace FS
namespace Stream

@[export lean_stream_of_handle]
def ofHandle (h : Handle) : Stream := {
  isEof   := Prim.Handle.isEof h,
  flush   := Prim.Handle.flush h,
  read    := Prim.Handle.read h,
  write   := Prim.Handle.write h,
  getLine := Prim.Handle.getLine h,
  putStr  := Prim.Handle.putStr h,
}

structure Buffer where
  data : ByteArray := ByteArray.empty
  pos  : Nat := 0

def ofBuffer (r : Ref Buffer) : Stream := {
  isEof   := do let b ← r.get; pure <| b.pos >= b.data.size,
  flush   := pure (),
  read    := fun n => r.modifyGet fun b =>
    let data := b.data.extract b.pos (b.pos + n.toNat)
    (data, { b with pos := b.pos + data.size }),
  write   := fun data => r.modify fun b =>
    -- set `exact` to `false` so that repeatedly writing to the stream does not impose quadratic run time
    { b with data := data.copySlice 0 b.data b.pos data.size false, pos := b.pos + data.size },
  getLine := r.modifyGet fun b =>
    let pos := match b.data.findIdx? (start := b.pos) fun u => u == 0 || u = '\n'.toNat.toUInt8 with
      -- include '\n', but not '\0'
      | some pos => if b.data.get! pos == 0 then pos else pos + 1
      | none     => b.data.size
    (String.fromUTF8Unchecked <| b.data.extract b.pos pos, { b with pos := pos }),
  putStr  := fun s => r.modify fun b =>
    let data := s.toUTF8
    { b with data := data.copySlice 0 b.data b.pos data.size false, pos := b.pos + data.size },
}
end Stream

/-- Run action with `stdin` emptied and `stdout+stderr` captured into a `String`. -/
def withIsolatedStreams (x : IO α) : IO (String × Except IO.Error α) := do
  let bIn ← mkRef { : Stream.Buffer }
  let bOut ← mkRef { : Stream.Buffer }
  let r ← withStdin (Stream.ofBuffer bIn) <|
    withStdout (Stream.ofBuffer bOut) <|
      withStderr (Stream.ofBuffer bOut) <|
        observing x
  let bOut ← bOut.get
  let out := String.fromUTF8Unchecked bOut.data
  pure (out, r)

end FS
end IO

universe u

namespace Lean

/-- Typeclass used for presenting the output of an `#eval` command. -/
class Eval (α : Type u) where
  -- We default `hideUnit` to `true`, but set it to `false` in the direct call from `#eval`
  -- so that `()` output is hidden in chained instances such as for some `m Unit`.
  -- We take `Unit → α` instead of `α` because ‵α` may contain effectful debugging primitives (e.g., `dbgTrace!`)
  eval : (Unit → α) → forall (hideUnit : optParam Bool true), IO Unit

instance [ToString α] : Eval α :=
  ⟨fun a _ => IO.println (toString (a ()))⟩

instance [Repr α] : Eval α :=
  ⟨fun a _ => IO.println (repr (a ()))⟩

instance : Eval Unit :=
  ⟨fun u hideUnit => if hideUnit then pure () else IO.println (repr (u ()))⟩

instance [Eval α] : Eval (IO α) :=
  ⟨fun x _ => do let a ← x (); Eval.eval (fun _ => a)⟩

@[noinline, nospecialize] def runEval [Eval α] (a : Unit → α) : IO (String × Except IO.Error Unit) :=
  IO.FS.withIsolatedStreams (Eval.eval a false)

end Lean

syntax "println! " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(println! $msg) =>
    if msg.getKind == Lean.interpolatedStrKind then
      `((IO.println (s! $msg) : IO Unit))
    else
      `((IO.println $msg : IO Unit))

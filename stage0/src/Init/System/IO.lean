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

instance monadExceptAdapter {ε ε'} : MonadExceptAdapter ε ε' (EIO ε) (EIO ε') :=
inferInstanceAs $ MonadExceptAdapter ε ε' (EStateM ε IO.RealWorld) (EStateM ε' IO.RealWorld)

@[inline] def EIO.catchExceptions {α ε} (x : EIO ε α) (h : ε → EIO Empty α) : EIO Empty α :=
fun s => match x s with
| EStateM.Result.ok a s     => EStateM.Result.ok a s
| EStateM.Result.error ex s => h ex s

instance (ε : Type) : Monad (EIO ε) := inferInstanceAs (Monad (EStateM ε IO.RealWorld))
instance (ε : Type) : MonadFinally (EIO ε) := inferInstanceAs (MonadFinally (EStateM ε IO.RealWorld))
instance (ε : Type) : MonadExceptOf ε (EIO ε) := inferInstanceAs (MonadExceptOf ε (EStateM ε IO.RealWorld))
instance (α ε : Type) : HasOrelse (EIO ε α) := ⟨MonadExcept.orelse⟩
instance {ε : Type} {α : Type} [Inhabited ε] : Inhabited (EIO ε α) :=
inferInstanceAs (Inhabited (EStateM ε IO.RealWorld α))

abbrev IO : Type → Type := EIO IO.Error

@[inline] def EIO.toIO {α ε} (f : ε → IO.Error) (x : EIO ε α) : IO α :=
x.adaptExcept f

@[inline] def IO.toEIO {α ε} (f : IO.Error → ε) (x : IO α) : EIO ε α :=
x.adaptExcept f

section
/- After we inline `EState.run'`, the closed term `((), ())` is generated, where the second `()`
   represents the "initial world". We don't want to cache this closed term. So, we disable
   the "extract closed terms" optimization. -/
set_option compiler.extract_closed false
@[inline] unsafe def unsafeIO {α : Type} (fn : IO α) : Except IO.Error α :=
match fn.run () with
| EStateM.Result.ok a _    => Except.ok a
| EStateM.Result.error e _ => Except.error e

end

@[extern "lean_io_timeit"]
constant timeit {α : Type} (msg : @& String) (fn : IO α) : IO α := arbitrary _

@[extern "lean_io_allocprof"]
constant allocprof {α : Type} (msg : @& String) (fn : IO α) : IO α := arbitrary _

/- Programs can execute IO actions during initialization that occurs before
   the `main` function is executed. The attribute `[init <action>]` specifies
   which IO action is executed to set the value of an opaque constant.

   The action `initializing` returns `true` iff it is invoked during initialization. -/
@[extern "lean_io_initializing"]
constant IO.initializing : IO Bool := arbitrary _

class MonadIO (m : Type → Type) :=
{ liftIO {α} : IO α → m α }

export MonadIO (liftIO)

instance monadIOTrans (m n) [MonadIO m] [MonadLift m n] : MonadIO n :=
{ liftIO := fun α x => liftM $ (liftIO x : m _) }

instance monadIOSelf : MonadIO IO :=
{ liftIO := fun α => id }

@[inline] def mkEIOMonadIO {ε ε'} [MonadIO (EIO ε)] (f : ε → ε') : MonadIO (EIO ε') :=
{ liftIO := fun α x => adaptExcept f (liftIO x : EIO ε α) }

namespace IO

def ofExcept {ε α : Type} [HasToString ε] (e : Except ε α) : IO α :=
match e with
| Except.ok a    => pure a
| Except.error e => throw (IO.userError (toString e))

def lazyPure {α : Type} (fn : Unit → α) : IO α :=
pure (fn ())

inductive FS.Mode
| read | write | readWrite | append

constant FS.Handle : Type := Unit

/--
  A pure-Lean abstraction of POSIX streams. We use `Stream`s for the standard streams stdin/stdout/stderr so we can
  capture output of `#eval` commands into memory. -/
structure FS.Stream :=
(isEof   : IO Bool)
(flush   : IO Unit)
(read    : forall (bytes : USize), IO ByteArray)
(write   : ByteArray → IO Unit)
(getLine : IO String)
(putStr  : String → IO Unit)

namespace Prim
open FS

@[extern "lean_get_stdin"]
constant getStdin  : IO FS.Stream := arbitrary _
@[extern "lean_get_stdout"]
constant getStdout : IO FS.Stream := arbitrary _
@[extern "lean_get_stderr"]
constant getStderr : IO FS.Stream := arbitrary _

@[extern "lean_get_set_stdin"]
constant setStdin  : FS.Stream → IO FS.Stream := arbitrary _
@[extern "lean_get_set_stdout"]
constant setStdout : FS.Stream → IO FS.Stream := arbitrary _
@[extern "lean_get_set_stderr"]
constant setStderr : FS.Stream → IO FS.Stream := arbitrary _

@[specialize] partial def iterate {α β : Type} : α → (α → IO (Sum α β)) → IO β
| a, f => do
  v ← f a;
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
let bin := if b then "b" else "t";
mode ++ bin

@[extern "lean_io_prim_handle_mk"]
constant Handle.mk (s : @& String) (mode : @& String) : IO Handle := arbitrary _
@[extern "lean_io_prim_handle_is_eof"]
constant Handle.isEof (h : @& Handle) : IO Bool := arbitrary _
@[extern "lean_io_prim_handle_flush"]
constant Handle.flush (h : @& Handle) : IO Unit := arbitrary _
@[extern "lean_io_prim_handle_read"]
constant Handle.read  (h : @& Handle) (bytes : USize) : IO ByteArray := arbitrary _
@[extern "lean_io_prim_handle_write"]
constant Handle.write (h : @& Handle) (buffer : @& ByteArray) : IO Unit := arbitrary _

@[extern "lean_io_prim_handle_get_line"]
constant Handle.getLine (h : @& Handle) : IO String := arbitrary _
@[extern "lean_io_prim_handle_put_str"]
constant Handle.putStr (h : @& Handle) (s : @& String) : IO Unit := arbitrary _

@[extern "lean_io_getenv"]
constant getEnv (var : @& String) : IO (Option String) := arbitrary _
@[extern "lean_io_realpath"]
constant realPath (fname : String) : IO String := arbitrary _
@[extern "lean_io_is_dir"]
constant isDir (fname : @& String) : IO Bool := arbitrary _
@[extern "lean_io_file_exists"]
constant fileExists (fname : @& String) : IO Bool := arbitrary _
@[extern "lean_io_app_dir"]
constant appPath : IO String := arbitrary _
@[extern "lean_io_current_dir"]
constant currentDir : IO String := arbitrary _

end Prim

namespace FS
variables {m : Type → Type} [Monad m] [MonadIO m]

def Handle.mk (s : String) (Mode : Mode) (bin : Bool := true) : m Handle :=
liftIO (Prim.Handle.mk s (Prim.fopenFlags Mode bin))

@[inline]
def withFile {α} (fn : String) (mode : Mode) (f : Handle → m α) : m α :=
Handle.mk fn mode >>= f

/-- returns whether the end of the file has been reached while reading a file.
`h.isEof` returns true /after/ the first attempt at reading past the end of `h`.
Once `h.isEof` is true, the reading `h` raises `IO.Error.eof`.
-/
def Handle.isEof : Handle → m Bool := liftIO ∘ Prim.Handle.isEof
def Handle.flush : Handle → m Unit := liftIO ∘ Prim.Handle.flush
def Handle.read (h : Handle) (bytes : Nat) : m ByteArray := liftIO (Prim.Handle.read h (USize.ofNat bytes))
def Handle.write (h : Handle) (s : ByteArray) : m Unit := liftIO (Prim.Handle.write h s)

def Handle.getLine : Handle → m String := liftIO ∘ Prim.Handle.getLine

def Handle.putStr (h : Handle) (s : String) : m Unit :=
liftIO $ Prim.Handle.putStr h s

def Handle.putStrLn (h : Handle) (s : String) : m Unit :=
h.putStr s *> h.putStr "\n"

-- TODO: support for binary files
partial def Handle.readToEndAux (h : Handle) : String → m String
| s => do
  line ← h.getLine;
  if line.length == 0 then pure s
  else Handle.readToEndAux (s ++ line)

-- TODO: support for binary files
def Handle.readToEnd (h : Handle) : m String :=
Handle.readToEndAux h ""

-- TODO: support for binary files
def readFile (fname : String) : m String := do
h ← Handle.mk fname Mode.read false;
h.readToEnd

partial def linesAux (h : Handle) : Array String → m (Array String)
| lines => do
  line ← h.getLine;
  if line.length == 0 then
    pure lines
  else if line.back == '\n' then
    let line := line.dropRight 1;
    let line := if System.Platform.isWindows && line.back == '\x0d' then line.dropRight 1 else line;
    linesAux $ lines.push line
  else
    pure $ lines.push line

def lines (fname : String) : m (Array String) := do
h ← Handle.mk fname Mode.read false;
linesAux h #[]

namespace Stream

def putStrLn (strm : FS.Stream) (s : String) : m Unit :=
liftIO (strm.putStr s) *> liftIO (strm.putStr "\n")

end Stream

end FS

section
variables {m : Type → Type} [Monad m] [MonadIO m]

def getStdin : m FS.Stream :=
liftIO Prim.getStdin

def getStdout : m FS.Stream :=
liftIO Prim.getStdout

def getStderr : m FS.Stream :=
liftIO Prim.getStderr

/-- Replaces the stdin stream of the current thread and returns its previous value. -/
def setStdin : FS.Stream → m FS.Stream :=
liftIO ∘ Prim.setStdin

/-- Replaces the stdout stream of the current thread and returns its previous value. -/
def setStdout : FS.Stream → m FS.Stream :=
liftIO ∘ Prim.setStdout

/-- Replaces the stderr stream of the current thread and returns its previous value. -/
def setStderr : FS.Stream → m FS.Stream :=
liftIO ∘ Prim.setStderr

def withStdin [MonadFinally m] {α} (h : FS.Stream) (x : m α) : m α := do
prev ← setStdin h;
finally x (discard $ setStdin prev)

def withStdout [MonadFinally m] {α} (h : FS.Stream) (x : m α) : m α := do
prev ← setStdout h;
finally x (discard $ setStdout prev)

def withStderr [MonadFinally m] {α} (h : FS.Stream) (x : m α) : m α := do
prev ← setStderr h;
finally x (discard $ setStderr prev)

def print {α} [HasToString α] (s : α) : m Unit := do
out ← getStdout;
liftIO $ out.putStr $ toString s

def println {α} [HasToString α] (s : α) : m Unit := print s *> print "\n"

@[export lean_io_println]
private def printlnAux (s : String) : IO Unit := println s

def eprint {α} [HasToString α] (s : α) : m Unit := do
out ← getStderr;
liftIO $ out.putStr $ toString s

def eprintln {α} [HasToString α] (s : α) : m Unit := eprint s *> eprint "\n"

def getEnv : String → m (Option String) := liftIO ∘ Prim.getEnv
def realPath : String → m String := liftIO ∘ Prim.realPath
def isDir : String → m Bool := liftIO ∘ Prim.isDir
def fileExists : String → m Bool := liftIO ∘ Prim.fileExists
def appPath : m String := liftIO Prim.appPath

def appDir : m String := do
p ← appPath;
realPath (System.FilePath.dirName p)

def currentDir : m String := liftIO Prim.currentDir

end

/-
namespace Proc
def child : Type :=
MonadIOProcess.child ioCore

def child.stdin : child → Handle :=
MonadIOProcess.stdin

def child.stdout : child → Handle :=
MonadIOProcess.stdout

def child.stderr : child → Handle :=
MonadIOProcess.stderr

def spawn (p : IO.process.spawnArgs) : IO child :=
MonadIOProcess.spawn ioCore p

def wait (c : child) : IO Nat :=
MonadIOProcess.wait c

end Proc
-/

structure AccessRight :=
(read write execution : Bool := false)

def AccessRight.flags (acc : AccessRight) : UInt32 :=
let r : UInt32 := if acc.read      then 0x4 else 0;
let w : UInt32 := if acc.write     then 0x2 else 0;
let x : UInt32 := if acc.execution then 0x1 else 0;
r.lor $ w.lor x

structure FileRight :=
(user group other : AccessRight := { })

def FileRight.flags (acc : FileRight) : UInt32 :=
let u : UInt32 := acc.user.flags.shiftLeft 6;
let g : UInt32 := acc.group.flags.shiftLeft 3;
let o : UInt32 := acc.other.flags;
u.lor $ g.lor o

@[extern "lean_chmod"]
constant Prim.setAccessRights (filename : @& String) (mode : UInt32) : IO Unit :=
arbitrary _

def setAccessRights (filename : String) (mode : FileRight) : IO Unit :=
Prim.setAccessRights filename mode.flags

/- References -/
abbrev Ref (α : Type) := ST.Ref IO.RealWorld α

instance st2eio {ε} : MonadLift (ST IO.RealWorld) (EIO ε) :=
⟨fun α x s => match x s with
 | EStateM.Result.ok a s     => EStateM.Result.ok a s
 | EStateM.Result.error ex _ => Empty.rec _ ex⟩

def mkRef {α : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST IO.RealWorld) m] (a : α) : m (IO.Ref α) :=
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

structure Buffer :=
(data : ByteArray := ByteArray.empty)
(pos : Nat := 0)

def ofBuffer (r : Ref Buffer) : Stream := {
  isEof   := do b ← r.get; pure $ b.pos >= b.data.size,
  flush   := pure (),
  read    := fun n => r.modifyGet fun b =>
    let data := b.data.extract b.pos (b.pos + n.toNat);
    (data, { b with pos := b.pos + data.size }),
  write   := fun data => r.modify fun b =>
    -- set `exact` to `false` so that repeatedly writing to the stream does not impose quadratic run time
    { b with data := data.copySlice 0 b.data b.pos data.size false, pos := b.pos + data.size },
  getLine := r.modifyGet fun b =>
    let pos := match b.data.findIdxAux (fun u => u == 0 || u = '\n'.toNat.toUInt8) b.pos with
    -- include '\n', but not '\0'
    | some pos => if b.data.get! pos == 0 then pos else pos + 1
    | none     => b.data.size;
    (String.fromUTF8Unchecked $ b.data.extract b.pos pos, { b with pos := pos }),
  putStr  := fun s => r.modify fun b =>
    let data := s.toUTF8;
    { b with data := data.copySlice 0 b.data b.pos data.size false, pos := b.pos + data.size },
}
end Stream

/-- Run action with `stdin` emptied and `stdout+stderr` captured into a `String`. -/
def withIsolatedStreams {α : Type} (x : IO α) : IO (String × Except IO.Error α) := do
bIn ← mkRef { : Stream.Buffer };
bOut ← mkRef { : Stream.Buffer };
r ← withStdin (Stream.ofBuffer bIn) $
  withStdout (Stream.ofBuffer bOut) $
    withStderr (Stream.ofBuffer bOut) $
      observing x;
bOut ← bOut.get;
let out := String.fromUTF8Unchecked bOut.data;
pure (out, r)

end FS
end IO

universe u

namespace Lean

/-- Typeclass used for presenting the output of an `#eval` command. -/
class HasEval (α : Type u) :=
-- We default `hideUnit` to `true`, but set it to `false` in the direct call from `#eval`
-- so that `()` output is hidden in chained instances such as for some `m Unit`.
(eval : α → forall (hideUnit : optParam Bool true), IO Unit)

instance HasRepr.hasEval {α : Type u} [HasRepr α] : HasEval α :=
⟨fun a _ => IO.println (repr a)⟩

instance Unit.hasEval : HasEval Unit :=
⟨fun u hideUnit => if hideUnit then pure () else IO.println (repr u)⟩

instance IO.HasEval {α : Type} [HasEval α] : HasEval (IO α) :=
⟨fun x _ => do a ← x; HasEval.eval a⟩

def runEval {α : Type u} [HasEval α] (a : α) : IO (String × Except IO.Error Unit) :=
IO.FS.withIsolatedStreams (HasEval.eval a false)

end Lean

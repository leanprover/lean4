/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.EState
import Init.Control.Reader
import Init.Data.String.Basic
import Init.Data.ByteArray
import Init.System.IOError
import Init.System.FilePath

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

@[inline] def EIO.adaptExcept {α ε ε'} (f : ε → ε') (x : EIO ε α) : EIO ε' α :=
EStateM.adaptExcept f x

@[inline] def EIO.catchExceptions {α ε} (x : EIO ε α) (h : ε → EIO Empty α) : EIO Empty α :=
fun s => match x s with
| EStateM.Result.ok a s     => EStateM.Result.ok a s
| EStateM.Result.error ex s => h ex s

instance (ε : Type) : Monad (EIO ε) := inferInstanceAs (Monad (EStateM ε IO.RealWorld))
instance (ε : Type) : MonadExcept ε (EIO ε) := inferInstanceAs (MonadExcept ε (EStateM ε IO.RealWorld))
instance (α ε : Type) : HasOrelse (EIO ε α) := ⟨MonadExcept.orelse⟩
instance {ε : Type} {α : Type} [Inhabited ε] : Inhabited (EIO ε α) :=
inferInstanceAs (Inhabited (EStateM ε IO.RealWorld α))

abbrev IO : Type → Type := EIO IO.Error

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

class MonadIO (m : Type → Type) extends HasMonadLiftT IO m, MonadExcept IO.Error m

instance : MonadIO IO := {  }

instance ExceptT.monadFail (m : Type → Type) [Monad m] [MonadExcept IO.Error m] : MonadFail m :=
⟨fun _ => throw ∘ IO.userError⟩

/- Omitted instances of MonadIO: OptionT, ExceptT and EStateT. The possibility for
errors introduces the risk that `withStdout` will not restore the previous handle when
an error is returned in the topmost monad. -/
instance ReaderT.monadIO {ρ} (m : Type → Type) [Monad m] [MonadIO m] : MonadIO (ReaderT ρ m) := {  }
instance StateT.monadIO {σ} (m : Type → Type) [Monad m] [MonadIO m] : MonadIO (StateT σ m) := {  }

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

namespace Prim
open FS

@[extern "lean_get_stdin"]
constant getStdin  : IO FS.Handle := arbitrary _
@[extern "lean_get_stderr"]
constant getStderr : IO FS.Handle := arbitrary _
@[extern "lean_get_stdout"]
constant getStdout : IO FS.Handle := arbitrary _

@[extern "lean_get_set_stdin"]
constant setStdin  : FS.Handle → IO FS.Handle := arbitrary _
@[extern "lean_get_set_stderr"]
constant setStderr : FS.Handle → IO FS.Handle := arbitrary _
@[extern "lean_get_set_stdout"]
constant setStdout : FS.Handle → IO FS.Handle := arbitrary _

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
-- TODO: replace `String` with byte buffer
@[extern "lean_io_prim_handle_read"]
constant Handle.read  (h : @& Handle) (bytes : USize) : IO ByteArray := arbitrary _
@[extern "lean_io_prim_handle_write"]
constant Handle.write (h : @& Handle) (buffer : @& ByteArray) : IO Unit := arbitrary _

@[extern "lean_io_prim_handle_read_byte"]
constant Handle.getByte  (h : @& Handle) : IO UInt8 := arbitrary _
@[extern "lean_io_prim_handle_write_byte"]
constant Handle.putByte (h : @& Handle) (c : UInt8) : IO Unit := arbitrary _

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

@[inline] def liftIO {m : Type → Type} {α : Type} [MonadIO m] (x : IO α) : m α :=
monadLift x
end Prim

namespace FS
variables {m : Type → Type} [Monad m] [MonadIO m]

def Handle.mk (s : String) (Mode : Mode) (bin : Bool := false) : m Handle :=
Prim.liftIO (Prim.Handle.mk s (Prim.fopenFlags Mode bin))

@[inline]
def withFile {α} (fn : String) (mode : Mode) (f : Handle → m α) : m α :=
Handle.mk fn mode >>= f

/-- returns whether the end of the file has been reached while reading a file.
`h.isEof` returns true /after/ the first attempt at reading past the end of `h`.
Once `h.isEof` is true, the reading `h` raises `IO.Error.eof`.
-/
def Handle.isEof : Handle → m Bool := Prim.liftIO ∘ Prim.Handle.isEof
def Handle.flush : Handle → m Unit := Prim.liftIO ∘ Prim.Handle.flush
def Handle.read (h : Handle) (bytes : Nat) : m ByteArray := Prim.liftIO (Prim.Handle.read h (USize.ofNat bytes))
def Handle.write (h : Handle) (s : ByteArray) : m Unit := Prim.liftIO (Prim.Handle.write h s)
def Handle.getByte (h : Handle) : m UInt8 := Prim.liftIO (Prim.Handle.getByte h)
def Handle.putByte (h : Handle) (b : UInt8) : m Unit := Prim.liftIO (Prim.Handle.putByte h b)

def Handle.getLine : Handle → m String := Prim.liftIO ∘ Prim.Handle.getLine

def Handle.putStr (h : Handle) (s : String) : m Unit :=
Prim.liftIO $ Prim.Handle.putStr h s

def Handle.putStrLn (h : Handle) (s : String) : m Unit :=
h.putStr s *> h.putStr "\n"

def Handle.readToEnd (h : Handle) : m String :=
Prim.liftIO $ Prim.iterate "" $ fun r => do
  done ← h.isEof;
  if done
  then pure (Sum.inr r) -- stop
  else do
    -- HACK: use less efficient `getLine` while `read` is broken
    c ← h.getLine;
    pure $ Sum.inl (r ++ c) -- continue

def Handle.readToExhaustion (h : Handle) : m String :=
Prim.liftIO $ Prim.iterate "" $ fun r => do
  done ← h.isEof;
  if done
  then pure (Sum.inr r) -- stop
  else do
    -- HACK: use less efficient `getLine` while `read` is broken
    catch (do
      c ← h.getLine;
      pure $ Sum.inl (r ++ c) /- continue -/ ) $
    fun e =>
      match e with
      | IO.Error.resourceExhausted _ _ _ => pure $ Sum.inr r
      | _ => throw e

end FS

section
variables {m : Type → Type} [Monad m] [MonadIO m]

def getStdout : m FS.Handle :=
Prim.liftIO Prim.getStdout

def getStderr : m FS.Handle :=
Prim.liftIO Prim.getStderr

def getStdin : m FS.Handle :=
Prim.liftIO Prim.getStdin

/- replaces the stdout handle and returns its previous value -/
def setStdout : FS.Handle → m FS.Handle :=
Prim.liftIO ∘ Prim.setStdout

/- see `setStdout` -/
def setStderr : FS.Handle → m FS.Handle :=
Prim.liftIO ∘ Prim.setStderr

/- see `setStdout` -/
def setStdin : FS.Handle → m FS.Handle :=
Prim.liftIO ∘ Prim.setStdin

def withStderr {α} (h : FS.Handle) (x : m α) : m α := do
prev ← setStderr h;
finally x (setStderr prev)

def withStdout {α} (h : FS.Handle) (x : m α) : m α := do
prev ← setStdout h;
finally x (setStdout prev)

def withStdin {α} (h : FS.Handle) (x : m α) : m α := do
prev ← setStdin h;
finally x (setStdin prev)

private def putStr (s : String) : m Unit := do
out ← getStdout;
out.putStr s

def print {α} [HasToString α] (s : α) : m Unit := putStr ∘ toString $ s
def println {α} [HasToString α] (s : α) : m Unit := print s *> putStr "\n"
def getEnv : String → m (Option String) := Prim.liftIO ∘ Prim.getEnv
def realPath : String → m String := Prim.liftIO ∘ Prim.realPath
def isDir : String → m Bool := Prim.liftIO ∘ Prim.isDir
def fileExists : String → m Bool := Prim.liftIO ∘ Prim.fileExists
def appPath : m String := Prim.liftIO Prim.appPath

def appDir : m String := do
p ← appPath;
realPath (System.FilePath.dirName p)

def readFile (fname : String) (bin := false) : m String := do
h ← FS.Handle.mk fname Mode.read bin;
r ← h.readToEnd;
pure r

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

structure Pipe :=
mk' :: (input : FS.Handle)
       (output : FS.Handle)

@[extern "lean_io_mk_pipe"]
constant Pipe.Prim.mk (nonBlocking : Bool) : IO Pipe := arbitrary _

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

def Pipe.mk {m} [MonadIO m] (nonBlocking : Bool := false) : m Pipe :=
Prim.liftIO $ Pipe.Prim.mk nonBlocking

def setAccessRights {m} [MonadIO m] (filename : String) (mode : FileRight) : m Unit :=
Prim.liftIO $ Prim.setAccessRights filename mode.flags


/- References -/
constant RefPointed (α : Type) : PointedType := arbitrary _
def Ref (α : Type) : Type := (RefPointed α).type
instance (α : Type) : Inhabited (Ref α) := ⟨(RefPointed α).val⟩

namespace Prim
@[extern "lean_io_mk_ref"]
constant mkRef {α : Type} (a : α) : IO (Ref α)                := arbitrary _
@[extern "lean_io_ref_get"]
constant Ref.get {α : Type} (r : @& Ref α) : IO α             := arbitrary _
@[extern "lean_io_ref_set"]
constant Ref.set {α : Type} (r : @& Ref α) (a : α) : IO Unit  := arbitrary _
@[extern "lean_io_ref_swap"]
constant Ref.swap {α : Type} (r : @& Ref α) (a : α) : IO α    := arbitrary _
@[extern "lean_io_ref_reset"]
constant Ref.reset {α : Type} (r : @& Ref α) : IO Unit        := arbitrary _
@[extern "lean_io_ref_ptr_eq"]
constant Ref.ptrEq {α : Type} (r1 r2 : @& Ref α) : IO Bool    := arbitrary _
end Prim

section
variables {m : Type → Type} [Monad m] [MonadIO m]
@[inline] def mkRef {α : Type} (a : α) : m (Ref α) :=  Prim.liftIO (Prim.mkRef a)
@[inline] def Ref.get {α : Type} (r : Ref α) : m α := Prim.liftIO (Prim.Ref.get r)
@[inline] def Ref.set {α : Type} (r : Ref α) (a : α) : m Unit := Prim.liftIO (Prim.Ref.set r a)
@[inline] def Ref.swap {α : Type} (r : Ref α) (a : α) : m α := Prim.liftIO (Prim.Ref.swap r a)
@[inline] def Ref.reset {α : Type} (r : Ref α) : m Unit := Prim.liftIO (Prim.Ref.reset r)
@[inline] def Ref.ptrEq {α : Type} (r1 r2 : Ref α) : m Bool := Prim.liftIO (Prim.Ref.ptrEq r1 r2)
@[inline] def Ref.modify {α : Type} (r : Ref α) (f : α → α) : m Unit := do
v ← r.get;
r.reset;
r.set (f v)
end
end IO

universe u

namespace Lean

/-- Typeclass used for presenting the output of an `#eval` command. -/
class HasEval (α : Type u) :=
(eval : α → IO Unit)

instance HasRepr.HasEval {α : Type u} [HasRepr α] : HasEval α :=
⟨fun a => IO.print (repr a)⟩

instance IO.HasEval {α : Type} [HasEval α] : HasEval (IO α) :=
⟨fun x => do a ← x; HasEval.eval a⟩

-- special case: do not print `()`
instance IOUnit.HasEval : HasEval (IO Unit) :=
⟨fun x => x⟩

end Lean

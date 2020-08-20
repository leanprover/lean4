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

def ST := EIO Empty

instance monadExceptAdapter {ε ε'} : MonadExceptAdapter ε ε' (EIO ε) (EIO ε') :=
inferInstanceAs $ MonadExceptAdapter ε ε' (EStateM ε IO.RealWorld) (EStateM ε' IO.RealWorld)

@[inline] def EIO.catchExceptions {α ε} (x : EIO ε α) (h : ε → EIO Empty α) : EIO Empty α :=
fun s => match x s with
| EStateM.Result.ok a s     => EStateM.Result.ok a s
| EStateM.Result.error ex s => h ex s

instance (ε : Type) : Monad (EIO ε) := inferInstanceAs (Monad (EStateM ε IO.RealWorld))
instance (ε : Type) : MonadExceptOf ε (EIO ε) := inferInstanceAs (MonadExceptOf ε (EStateM ε IO.RealWorld))
instance (α ε : Type) : HasOrelse (EIO ε α) := ⟨MonadExcept.orelse⟩
instance {ε : Type} {α : Type} [Inhabited ε] : Inhabited (EIO ε α) :=
inferInstanceAs (Inhabited (EStateM ε IO.RealWorld α))
instance : Monad ST := inferInstanceAs (Monad (EIO Empty))

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

instance monadIOSelf : MonadIO IO :=
{ liftIO := fun α => id }

/- Omitted instances of MonadIO: OptionT, ExceptT and EStateT. The possibility for
errors introduces the risk that `withStdout` will not restore the previous handle when
an error is returned in the topmost monad. -/
instance ReaderT.monadIO {ρ} (m : Type → Type) [Monad m] [MonadIO m] : MonadIO (ReaderT ρ m) :=
{ liftIO := fun α x => liftM (liftIO x : m α) }
instance StateT.monadIO {σ} (m : Type → Type) [Monad m] [MonadIO m] : MonadIO (StateT σ m) :=
{ liftIO := fun α x => liftM (liftIO x : m α) }

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

namespace Prim
open FS

@[extern "lean_get_stdin"]
constant stdin  : IO FS.Handle := arbitrary _
@[extern "lean_get_stdout"]
constant stdout : IO FS.Handle := arbitrary _
@[extern "lean_get_stderr"]
constant stderr : IO FS.Handle := arbitrary _

/-- Run action with `stdin` closed and `stdout+stderr` captured into a `String`. -/
@[extern "lean_with_isolated_streams"]
constant withIsolatedStreams {α : Type} : IO α → IO (String × Except IO.Error α) := arbitrary _

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

end FS

section
variables {m : Type → Type} [Monad m] [MonadIO m]

def stdin : m FS.Handle :=
liftIO Prim.stdin

def stdout : m FS.Handle :=
liftIO Prim.stdout

def stderr : m FS.Handle :=
liftIO Prim.stderr

def print {α} [HasToString α] (s : α) : m Unit := do
out ← stdout;
out.putStr $ toString s

def println {α} [HasToString α] (s : α) : m Unit := print s *> print "\n"

def eprint {α} [HasToString α] (s : α) : m Unit := do
out ← stderr;
out.putStr $ toString s

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
constant RefPointed : PointedType.{0} := arbitrary _

structure Ref (α : Type) : Type :=
(ref : RefPointed.type) (h : Nonempty α)

instance Ref.inhabited {α} [Inhabited α] : Inhabited (Ref α) :=
⟨{ ref := RefPointed.val, h := Nonempty.intro $ arbitrary _}⟩

namespace Prim

/- Auxiliary definition for showing that `EIO ε α` is inhabited when we have a `Ref α` -/
private noncomputable def inhabitedFromRef {α} (r : Ref α) : ST α :=
pure $ (Classical.inhabitedOfNonempty r.h).default


@[extern "lean_io_mk_ref"]
constant mkRef {α} (a : α) : ST (Ref α) := pure { ref := RefPointed.val, h := Nonempty.intro a }
@[extern "lean_io_ref_get"]
constant Ref.get {α} (r : @& Ref α) : ST α := inhabitedFromRef r
@[extern "lean_io_ref_set"]
constant Ref.set {α} (r : @& Ref α) (a : α) : ST Unit := arbitrary _
@[extern "lean_io_ref_swap"]
constant Ref.swap {α} (r : @& Ref α) (a : α) : ST α := inhabitedFromRef r
@[extern "lean_io_ref_take"]
unsafe constant Ref.take {α} (r : @& Ref α) : ST α := inhabitedFromRef r
@[extern "lean_io_ref_ptr_eq"]
constant Ref.ptrEq {α} (r1 r2 : @& Ref α) : ST Bool := arbitrary _
@[inline] unsafe def Ref.modifyUnsafe {α : Type} (r : Ref α) (f : α → α) : ST Unit := do
v ← Ref.take r;
Ref.set r (f v)

@[inline] unsafe def Ref.modifyGetUnsafe {α : Type} {β : Type} (r : Ref α) (f : α → β × α) : ST β := do
v ← Ref.take r;
let (b, a) := f v;
Ref.set r a;
pure b

@[implementedBy Ref.modifyUnsafe]
def Ref.modify {α : Type} (r : Ref α) (f : α → α) : ST Unit := do
v ← Ref.get r;
Ref.set r (f v)

@[implementedBy Ref.modifyGetUnsafe]
def Ref.modifyGet {α : Type} {β : Type} (r : Ref α) (f : α → β × α) : ST β := do
v ← Ref.get r;
let (b, a) := f v;
Ref.set r a;
pure b

end Prim

section

@[inline] private def liftST {ε α} (x : ST α) : EIO ε α :=
fun s => match x s with
  | r@(EStateM.Result.error e _) => Empty.rec _ e
  | EStateM.Result.ok a s        => EStateM.Result.ok a s

instance ST.monadLift {ε} : HasMonadLift ST (EIO ε) :=
{ monadLift := fun α => liftST }

variables {m : Type → Type} [Monad m] [HasMonadLiftT ST m]

@[inline] def mkRef {α : Type} (a : α) : m (Ref α) :=  liftM $ Prim.mkRef a
@[inline] def Ref.get {α : Type} (r : Ref α) : m α := liftM $ Prim.Ref.get r
@[inline] def Ref.set {α : Type} (r : Ref α) (a : α) : m Unit := liftM $ Prim.Ref.set r a
@[inline] def Ref.swap {α : Type} (r : Ref α) (a : α) : m α := liftM $ Prim.Ref.swap r a
@[inline] unsafe def Ref.take {α : Type} (r : Ref α) : m α := liftM $ Prim.Ref.take r
@[inline] def Ref.ptrEq {α : Type} (r1 r2 : Ref α) : m Bool := liftM $ Prim.Ref.ptrEq r1 r2
@[inline] def Ref.modify {α : Type} (r : Ref α) (f : α → α) : m Unit := liftM $ Prim.Ref.modify r f
@[inline] def Ref.modifyGet {α : Type} {β : Type} (r : Ref α) (f : α → β × α) : m β := liftM $ Prim.Ref.modifyGet r f

end

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

end Lean

/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.Estate init.data.String.basic init.fix

/-- Like https://hackage.haskell.org/package/ghc-Prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `IO` operations. -/
constant IO.RealWorld : Type := unit

/- TODO(Leo): mark it as an opaque definition. Reason: prevent
   functions defined in other modules from accessing `IO.RealWorld`.
   We don't want action such as
   ```
   def getWorld : IO (IO.RealWorld) := get
   ```
-/
@[derive Monad MonadExcept]
def EIO (ε : Type) : Type → Type := Estate ε IO.RealWorld

instance {ε : Type} {α : Type} [Inhabited ε] : Inhabited (EIO ε α) :=
inferInstanceAs (Inhabited (Estate ε IO.RealWorld α))

/-
In the future, we may want to give more concrete data
like in https://doc.rust-lang.org/std/IO/enum.ErrorKind.html
-/
@[derive HasToString Inhabited]
def IO.error := String

abbrev IO : Type → Type := EIO IO.error

@[extern "lean_io_unsafe"]
constant unsafeIO {α : Type} (fn : IO α) : Option α := default _

@[extern 4 "lean_io_timeit"]
constant timeit {α : Type} (msg : @& String) (fn : IO α) : IO α := default _

@[extern 4 "lean_io_allocprof"]
constant allocprof {α : Type} (msg : @& String) (fn : IO α) : IO α := default _

abbrev monadIO (m : Type → Type) := HasMonadLiftT IO m

def ioOfExcept {ε α : Type} [HasToString ε] (e : Except ε α) : IO α :=
match e with
| Except.ok a    := pure a
| Except.error e := throw $ toString e

namespace IO

def lazyPure {α : Type} (fn : unit → α) : IO α :=
pure (fn ())

inductive Fs.Mode
| read | write | readWrite | append

constant Fs.handle : Type := unit

namespace Prim
open Fs

def iterateAux {α β : Type} (f : α → IO (Sum α β)) : (α → IO β) → (α → IO β)
| rec a :=
  do v ← f a,
  match v with
  | Sum.inl a := rec a
  | Sum.inr b := pure b

@[specialize] def iterate {α β : Type} (a : α) (f : α → IO (Sum α β)) : IO β :=
fixCore (λ _, throw "deep recursion") (iterateAux f) a

@[extern 2 "lean_io_prim_put_str"]
constant putStr (s: @& String) : IO unit := default _
@[extern 1 "lean_io_prim_get_line"]
constant getLine : IO String := default _
@[extern 4 "lean_io_prim_handle_mk"]
constant handle.mk (s : @& String) (m : Mode) (bin : Bool := ff) : IO handle := default _
@[extern 2 "lean_io_prim_handle_is_eof"]
constant handle.isEof (h : @& handle) : IO Bool := default _
@[extern 2 "lean_io_prim_handle_flush"]
constant handle.flush (h : @& handle) : IO unit := default _
@[extern 2 "lean_io_prim_handle_close"]
constant handle.close (h : @& handle) : IO unit := default _
-- TODO: replace `String` with byte buffer
-- constant handle.read : handle → Nat → EIO String
-- constant handle.write : handle → String → EIO unit
@[extern 2 "lean_io_prim_handle_get_line"]
constant handle.getLine (h : @& handle) : IO String := default _

@[inline] def liftIO {m : Type → Type} {α : Type} [monadIO m] (x : IO α) : m α :=
monadLift x
end Prim

section
variables {m : Type → Type} [Monad m] [monadIO m]

private def putStr : String → m unit :=
Prim.liftIO ∘ Prim.putStr

def print {α} [HasToString α] (s : α) : m unit :=
putStr ∘ toString $ s

def println {α} [HasToString α] (s : α) : m unit :=
print s *> putStr "\n"
end

namespace Fs
variables {m : Type → Type} [Monad m] [monadIO m]

def handle.mk (s : String) (Mode : Mode) (bin : Bool := ff) : m handle := Prim.liftIO (Prim.handle.mk s Mode bin)
def handle.isEof : handle → m Bool := Prim.liftIO ∘ Prim.handle.isEof
def handle.flush : handle → m unit := Prim.liftIO ∘ Prim.handle.flush
def handle.close : handle → m unit := Prim.liftIO ∘ Prim.handle.flush
-- def handle.read (h : handle) (bytes : Nat) : m String := Prim.liftEIO (Prim.handle.read h bytes)
-- def handle.write (h : handle) (s : String) : m unit := Prim.liftEIO (Prim.handle.write h s)
def handle.getLine : handle → m String := Prim.liftIO ∘ Prim.handle.getLine

/-
def getChar (h : handle) : m Char :=
do b ← h.read 1,
   if b.isEmpty then fail "getChar failed"
   else pure b.mkIterator.curr
-/

-- def handle.putChar (h : handle) (c : Char) : m unit :=
-- h.write (toString c)

-- def handle.putStr (h : handle) (s : String) : m unit :=
-- h.write s

-- def handle.putStrLn (h : handle) (s : String) : m unit :=
-- h.putStr s *> h.putStr "\n"

def handle.readToEnd (h : handle) : m String :=
Prim.liftIO $ Prim.iterate "" $ λ r, do
  done ← h.isEof,
  if done
  then pure (Sum.inr r) -- stop
  else do
    -- HACK: use less efficient `getLine` while `read` is broken
    c ← h.getLine,
    pure $ Sum.inl (r ++ c) -- continue

def readFile (fname : String) (bin := ff) : m String :=
do h ← handle.mk fname Mode.read bin,
   r ← h.readToEnd,
   h.close,
   pure r

-- def writeFile (fname : String) (data : String) (bin := ff) : m unit :=
-- do h ← handle.mk fname Mode.write bin,
--   h.write data,
--   h.close

end Fs

-- constant stdin : IO Fs.handle
-- constant stderr : IO Fs.handle
-- constant stdout : IO Fs.handle

/-
namespace Proc
def child : Type :=
monadIOProcess.child ioCore

def child.stdin : child → handle :=
monadIOProcess.stdin

def child.stdout : child → handle :=
monadIOProcess.stdout

def child.stderr : child → handle :=
monadIOProcess.stderr

def spawn (p : IO.process.spawnArgs) : IO child :=
monadIOProcess.spawn ioCore p

def wait (c : child) : IO Nat :=
monadIOProcess.wait c

end Proc
-/


/- References -/
constant RefPointed : PointedType := default _
def Ref (α : Type) : Type := RefPointed.Type
instance (α : Type) : Inhabited (Ref α) :=
⟨RefPointed.val⟩

namespace Prim
@[extern 3 cpp inline "Lean::io_mk_ref(#2, #3)"]
constant mkRef {α : Type} (a : α) : IO (Ref α)                := default _
@[extern 3 cpp inline "Lean::io_ref_read(#2, #3)"]
constant Ref.read {α : Type} (r : @& Ref α) : IO α             := default _
@[extern 4 cpp inline "Lean::io_ref_write(#2, #3, #4)"]
constant Ref.write {α : Type} (r : @& Ref α) (a : α) : IO unit := default _
@[extern 4 cpp inline "Lean::io_ref_swap(#2, #3, #4)"]
constant Ref.swap {α : Type} (r : @& Ref α) (a : α) : IO α     := default _
@[extern 3 cpp inline "Lean::io_ref_reset(#2, #3)"]
constant Ref.reset {α : Type} (r : @& Ref α) : IO unit         := default _
end Prim

section
variables {m : Type → Type} [Monad m] [monadIO m]
@[inline] def mkRef {α : Type} (a : α) : m (Ref α) :=  Prim.liftIO (Prim.mkRef a)
@[inline] def Ref.read {α : Type} (r : Ref α) : m α := Prim.liftIO (Prim.Ref.read r)
@[inline] def Ref.write {α : Type} (r : Ref α) (a : α) : m unit := Prim.liftIO (Prim.Ref.write r a)
@[inline] def Ref.swap {α : Type} (r : Ref α) (a : α) : m α := Prim.liftIO (Prim.Ref.swap r a)
@[inline] def Ref.reset {α : Type} (r : Ref α) : m unit := Prim.liftIO (Prim.Ref.reset r)
@[inline] def Ref.modify {α : Type} (r : Ref α) (f : α → α) : m unit :=
do v ← r.read,
   r.reset,
   r.write (f v)
end
end IO

/-
/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `String` which is then returned. -/
def IO.cmd (args : IO.process.spawnArgs) : IO String :=
do child ← IO.Proc.spawn { stdout := IO.process.stdio.piped, ..args },
  s ← IO.Fs.readToEnd child.stdout,
  IO.Fs.close child.stdout,
  exitv ← IO.Proc.wait child,
  if exitv ≠ 0 then IO.fail $ "process exited with status " ++ repr exitv else pure (),
  pure s
-/

universe u

/-- Typeclass used for presenting the output of an `#eval` command. -/
class HasEval (α : Type u) :=
(eval : α → IO unit)

instance HasRepr.HasEval {α : Type u} [HasRepr α] : HasEval α :=
⟨λ a, IO.println (repr a)⟩

instance IO.HasEval {α : Type} [HasEval α] : HasEval (IO α) :=
⟨λ x, do a ← x, HasEval.eval a⟩

-- special case: do not print `()`
instance ioUnit.HasEval : HasEval (IO unit) :=
⟨λ x, x⟩

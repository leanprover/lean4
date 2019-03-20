/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.Estate init.data.String.basic init.fix

/-- Like https://hackage.haskell.org/package/ghc-Prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `Io` operations. -/
constant Io.realWorld : Type := unit

/- TODO(Leo): mark it as an opaque definition. Reason: prevent
   functions defined in other modules from accessing `Io.realWorld`.
   We don't want action such as
   ```
   def getWorld : Io (Io.realWorld) := get
   ```
-/
@[derive Monad MonadExcept]
def Eio (ε : Type) : Type → Type := Estate ε Io.realWorld

instance {ε : Type} {α : Type} [Inhabited ε] : Inhabited (Eio ε α) :=
inferInstanceAs (Inhabited (Estate ε Io.realWorld α))

/-
In the future, we may want to give more concrete data
like in https://doc.rust-lang.org/std/Io/enum.ErrorKind.html
-/
@[derive HasToString Inhabited]
def Io.error := String

abbrev Io : Type → Type := Eio Io.error

@[extern "lean_io_unsafe"]
constant unsafeIo {α : Type} (fn : Io α) : Option α := default _

@[extern 4 "lean_io_timeit"]
constant timeit {α : Type} (msg : @& String) (fn : Io α) : Io α := default _

@[extern 4 "lean_io_allocprof"]
constant allocprof {α : Type} (msg : @& String) (fn : Io α) : Io α := default _

abbrev monadIo (m : Type → Type) := HasMonadLiftT Io m

def ioOfExcept {ε α : Type} [HasToString ε] (e : Except ε α) : Io α :=
match e with
| Except.ok a    := pure a
| Except.error e := throw $ toString e

namespace Io

def lazyPure {α : Type} (fn : unit → α) : Io α :=
pure (fn ())

inductive Fs.Mode
| read | write | readWrite | append

constant Fs.handle : Type := unit

namespace Prim
open Fs

def iterateAux {α β : Type} (f : α → Io (Sum α β)) : (α → Io β) → (α → Io β)
| rec a :=
  do v ← f a,
  match v with
  | Sum.inl a := rec a
  | Sum.inr b := pure b

@[specialize] def iterate {α β : Type} (a : α) (f : α → Io (Sum α β)) : Io β :=
fixCore (λ _, throw "deep recursion") (iterateAux f) a

@[extern 2 "lean_io_prim_put_str"]
constant putStr (s: @& String) : Io unit := default _
@[extern 1 "lean_io_prim_get_line"]
constant getLine : Io String := default _
@[extern 4 "lean_io_prim_handle_mk"]
constant handle.mk (s : @& String) (m : Mode) (bin : Bool := ff) : Io handle := default _
@[extern 2 "lean_io_prim_handle_is_eof"]
constant handle.isEof (h : @& handle) : Io Bool := default _
@[extern 2 "lean_io_prim_handle_flush"]
constant handle.flush (h : @& handle) : Io unit := default _
@[extern 2 "lean_io_prim_handle_close"]
constant handle.close (h : @& handle) : Io unit := default _
-- TODO: replace `String` with byte buffer
-- constant handle.read : handle → Nat → Eio String
-- constant handle.write : handle → String → Eio unit
@[extern 2 "lean_io_prim_handle_get_line"]
constant handle.getLine (h : @& handle) : Io String := default _

@[inline] def liftIo {m : Type → Type} {α : Type} [monadIo m] (x : Io α) : m α :=
monadLift x
end Prim

section
variables {m : Type → Type} [Monad m] [monadIo m]

private def putStr : String → m unit :=
Prim.liftIo ∘ Prim.putStr

def print {α} [HasToString α] (s : α) : m unit :=
putStr ∘ toString $ s

def println {α} [HasToString α] (s : α) : m unit :=
print s *> putStr "\n"
end

namespace Fs
variables {m : Type → Type} [Monad m] [monadIo m]

def handle.mk (s : String) (Mode : Mode) (bin : Bool := ff) : m handle := Prim.liftIo (Prim.handle.mk s Mode bin)
def handle.isEof : handle → m Bool := Prim.liftIo ∘ Prim.handle.isEof
def handle.flush : handle → m unit := Prim.liftIo ∘ Prim.handle.flush
def handle.close : handle → m unit := Prim.liftIo ∘ Prim.handle.flush
-- def handle.read (h : handle) (bytes : Nat) : m String := Prim.liftEio (Prim.handle.read h bytes)
-- def handle.write (h : handle) (s : String) : m unit := Prim.liftEio (Prim.handle.write h s)
def handle.getLine : handle → m String := Prim.liftIo ∘ Prim.handle.getLine

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
Prim.liftIo $ Prim.iterate "" $ λ r, do
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

-- constant stdin : Io Fs.handle
-- constant stderr : Io Fs.handle
-- constant stdout : Io Fs.handle

/-
namespace Proc
def child : Type :=
monadIoProcess.child ioCore

def child.stdin : child → handle :=
monadIoProcess.stdin

def child.stdout : child → handle :=
monadIoProcess.stdout

def child.stderr : child → handle :=
monadIoProcess.stderr

def spawn (p : Io.process.spawnArgs) : Io child :=
monadIoProcess.spawn ioCore p

def wait (c : child) : Io Nat :=
monadIoProcess.wait c

end Proc
-/


/- References -/
constant refPointed : PointedType := default _
def ref (α : Type) : Type := refPointed.Type
instance (α : Type) : Inhabited (ref α) :=
⟨refPointed.val⟩

namespace Prim
@[extern 3 cpp inline "Lean::io_mk_ref(#2, #3)"]
constant mkRef {α : Type} (a : α) : Io (ref α)                := default _
@[extern 3 cpp inline "Lean::io_ref_read(#2, #3)"]
constant ref.read {α : Type} (r : @& ref α) : Io α             := default _
@[extern 4 cpp inline "Lean::io_ref_write(#2, #3, #4)"]
constant ref.write {α : Type} (r : @& ref α) (a : α) : Io unit := default _
@[extern 4 cpp inline "Lean::io_ref_swap(#2, #3, #4)"]
constant ref.swap {α : Type} (r : @& ref α) (a : α) : Io α     := default _
@[extern 3 cpp inline "Lean::io_ref_reset(#2, #3)"]
constant ref.reset {α : Type} (r : @& ref α) : Io unit         := default _
end Prim

section
variables {m : Type → Type} [Monad m] [monadIo m]
@[inline] def mkRef {α : Type} (a : α) : m (ref α) :=  Prim.liftIo (Prim.mkRef a)
@[inline] def ref.read {α : Type} (r : ref α) : m α := Prim.liftIo (Prim.ref.read r)
@[inline] def ref.write {α : Type} (r : ref α) (a : α) : m unit := Prim.liftIo (Prim.ref.write r a)
@[inline] def ref.swap {α : Type} (r : ref α) (a : α) : m α := Prim.liftIo (Prim.ref.swap r a)
@[inline] def ref.reset {α : Type} (r : ref α) : m unit := Prim.liftIo (Prim.ref.reset r)
@[inline] def ref.modify {α : Type} (r : ref α) (f : α → α) : m unit :=
do v ← ref.read r,
   ref.reset r,
   ref.write r (f v)
end
end Io

/-
/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `String` which is then returned. -/
def Io.cmd (args : Io.process.spawnArgs) : Io String :=
do child ← Io.Proc.spawn { stdout := Io.process.stdio.piped, ..args },
  s ← Io.Fs.readToEnd child.stdout,
  Io.Fs.close child.stdout,
  exitv ← Io.Proc.wait child,
  if exitv ≠ 0 then Io.fail $ "process exited with status " ++ repr exitv else pure (),
  pure s
-/

universe u

/-- Typeclass used for presenting the output of an `#eval` command. -/
class HasEval (α : Type u) :=
(eval : α → Io unit)

instance HasRepr.HasEval {α : Type u} [HasRepr α] : HasEval α :=
⟨λ a, Io.println (repr a)⟩

instance Io.HasEval {α : Type} [HasEval α] : HasEval (Io α) :=
⟨λ x, do a ← x, HasEval.eval a⟩

-- special case: do not print `()`
instance ioUnit.HasEval : HasEval (Io unit) :=
⟨λ x, x⟩

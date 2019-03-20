/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.estate init.data.string.basic init.fix

/-- Like https://hackage.haskell.org/package/ghc-prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `io` operations. -/
constant io.realWorld : Type := unit

/- TODO(Leo): mark it as an opaque definition. Reason: prevent
   functions defined in other modules from accessing `io.realWorld`.
   We don't want action such as
   ```
   def getWorld : io (io.realWorld) := get
   ```
-/
@[derive monad monadExcept]
def eio (ε : Type) : Type → Type := estate ε io.realWorld

instance {ε : Type} {α : Type} [inhabited ε] : inhabited (eio ε α) :=
inferInstanceAs (inhabited (estate ε io.realWorld α))

/-
In the future, we may want to give more concrete data
like in https://doc.rust-lang.org/std/io/enum.ErrorKind.html
-/
@[derive hasToString inhabited]
def io.error := string

abbrev io : Type → Type := eio io.error

@[extern "lean_io_unsafe"]
constant unsafeIo {α : Type} (fn : io α) : option α := default _

@[extern 4 "lean_io_timeit"]
constant timeit {α : Type} (msg : @& string) (fn : io α) : io α := default _

@[extern 4 "lean_io_allocprof"]
constant allocprof {α : Type} (msg : @& string) (fn : io α) : io α := default _

abbrev monadIo (m : Type → Type) := hasMonadLiftT io m

def ioOfExcept {ε α : Type} [hasToString ε] (e : except ε α) : io α :=
match e with
| except.ok a    := pure a
| except.error e := throw $ toString e

namespace io

def lazyPure {α : Type} (fn : unit → α) : io α :=
pure (fn ())

inductive fs.mode
| read | write | readWrite | append

constant fs.handle : Type := unit

namespace prim
open fs

def iterateAux {α β : Type} (f : α → io (sum α β)) : (α → io β) → (α → io β)
| rec a :=
  do v ← f a,
  match v with
  | sum.inl a := rec a
  | sum.inr b := pure b

@[specialize] def iterate {α β : Type} (a : α) (f : α → io (sum α β)) : io β :=
fixCore (λ _, throw "deep recursion") (iterateAux f) a

@[extern 2 "lean_io_prim_put_str"]
constant putStr (s: @& string) : io unit := default _
@[extern 1 "lean_io_prim_get_line"]
constant getLine : io string := default _
@[extern 4 "lean_io_prim_handle_mk"]
constant handle.mk (s : @& string) (m : mode) (bin : bool := ff) : io handle := default _
@[extern 2 "lean_io_prim_handle_is_eof"]
constant handle.isEof (h : @& handle) : io bool := default _
@[extern 2 "lean_io_prim_handle_flush"]
constant handle.flush (h : @& handle) : io unit := default _
@[extern 2 "lean_io_prim_handle_close"]
constant handle.close (h : @& handle) : io unit := default _
-- TODO: replace `string` with byte buffer
-- constant handle.read : handle → nat → eio string
-- constant handle.write : handle → string → eio unit
@[extern 2 "lean_io_prim_handle_get_line"]
constant handle.getLine (h : @& handle) : io string := default _

@[inline] def liftIo {m : Type → Type} {α : Type} [monadIo m] (x : io α) : m α :=
monadLift x
end prim

section
variables {m : Type → Type} [monad m] [monadIo m]

private def putStr : string → m unit :=
prim.liftIo ∘ prim.putStr

def print {α} [hasToString α] (s : α) : m unit :=
putStr ∘ toString $ s

def println {α} [hasToString α] (s : α) : m unit :=
print s *> putStr "\n"
end

namespace fs
variables {m : Type → Type} [monad m] [monadIo m]

def handle.mk (s : string) (mode : mode) (bin : bool := ff) : m handle := prim.liftIo (prim.handle.mk s mode bin)
def handle.isEof : handle → m bool := prim.liftIo ∘ prim.handle.isEof
def handle.flush : handle → m unit := prim.liftIo ∘ prim.handle.flush
def handle.close : handle → m unit := prim.liftIo ∘ prim.handle.flush
-- def handle.read (h : handle) (bytes : nat) : m string := prim.liftEio (prim.handle.read h bytes)
-- def handle.write (h : handle) (s : string) : m unit := prim.liftEio (prim.handle.write h s)
def handle.getLine : handle → m string := prim.liftIo ∘ prim.handle.getLine

/-
def getChar (h : handle) : m char :=
do b ← h.read 1,
   if b.isEmpty then fail "getChar failed"
   else pure b.mkIterator.curr
-/

-- def handle.putChar (h : handle) (c : char) : m unit :=
-- h.write (toString c)

-- def handle.putStr (h : handle) (s : string) : m unit :=
-- h.write s

-- def handle.putStrLn (h : handle) (s : string) : m unit :=
-- h.putStr s *> h.putStr "\n"

def handle.readToEnd (h : handle) : m string :=
prim.liftIo $ prim.iterate "" $ λ r, do
  done ← h.isEof,
  if done
  then pure (sum.inr r) -- stop
  else do
    -- HACK: use less efficient `getLine` while `read` is broken
    c ← h.getLine,
    pure $ sum.inl (r ++ c) -- continue

def readFile (fname : string) (bin := ff) : m string :=
do h ← handle.mk fname mode.read bin,
   r ← h.readToEnd,
   h.close,
   pure r

-- def writeFile (fname : string) (data : string) (bin := ff) : m unit :=
-- do h ← handle.mk fname mode.write bin,
--   h.write data,
--   h.close

end fs

-- constant stdin : io fs.handle
-- constant stderr : io fs.handle
-- constant stdout : io fs.handle

/-
namespace proc
def child : Type :=
monadIoProcess.child ioCore

def child.stdin : child → handle :=
monadIoProcess.stdin

def child.stdout : child → handle :=
monadIoProcess.stdout

def child.stderr : child → handle :=
monadIoProcess.stderr

def spawn (p : io.process.spawnArgs) : io child :=
monadIoProcess.spawn ioCore p

def wait (c : child) : io nat :=
monadIoProcess.wait c

end proc
-/


/- References -/
constant refPointed : pointedType := default _
def ref (α : Type) : Type := refPointed.type
instance (α : Type) : inhabited (ref α) :=
⟨refPointed.val⟩

namespace prim
@[extern 3 cpp inline "lean::io_mk_ref(#2, #3)"]
constant mkRef {α : Type} (a : α) : io (ref α)                := default _
@[extern 3 cpp inline "lean::io_ref_read(#2, #3)"]
constant ref.read {α : Type} (r : @& ref α) : io α             := default _
@[extern 4 cpp inline "lean::io_ref_write(#2, #3, #4)"]
constant ref.write {α : Type} (r : @& ref α) (a : α) : io unit := default _
@[extern 4 cpp inline "lean::io_ref_swap(#2, #3, #4)"]
constant ref.swap {α : Type} (r : @& ref α) (a : α) : io α     := default _
@[extern 3 cpp inline "lean::io_ref_reset(#2, #3)"]
constant ref.reset {α : Type} (r : @& ref α) : io unit         := default _
end prim

section
variables {m : Type → Type} [monad m] [monadIo m]
@[inline] def mkRef {α : Type} (a : α) : m (ref α) :=  prim.liftIo (prim.mkRef a)
@[inline] def ref.read {α : Type} (r : ref α) : m α := prim.liftIo (prim.ref.read r)
@[inline] def ref.write {α : Type} (r : ref α) (a : α) : m unit := prim.liftIo (prim.ref.write r a)
@[inline] def ref.swap {α : Type} (r : ref α) (a : α) : m α := prim.liftIo (prim.ref.swap r a)
@[inline] def ref.reset {α : Type} (r : ref α) : m unit := prim.liftIo (prim.ref.reset r)
@[inline] def ref.modify {α : Type} (r : ref α) (f : α → α) : m unit :=
do v ← ref.read r,
   ref.reset r,
   ref.write r (f v)
end
end io

/-
/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `string` which is then returned. -/
def io.cmd (args : io.process.spawnArgs) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  s ← io.fs.readToEnd child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  if exitv ≠ 0 then io.fail $ "process exited with status " ++ repr exitv else pure (),
  pure s
-/

universe u

/-- Typeclass used for presenting the output of an `#eval` command. -/
class hasEval (α : Type u) :=
(eval : α → io unit)

instance hasRepr.hasEval {α : Type u} [hasRepr α] : hasEval α :=
⟨λ a, io.println (repr a)⟩

instance io.hasEval {α : Type} [hasEval α] : hasEval (io α) :=
⟨λ x, do a ← x, hasEval.eval a⟩

-- special case: do not print `()`
instance ioUnit.hasEval : hasEval (io unit) :=
⟨λ x, x⟩

/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.state init.control.except init.data.string.basic init.fix

/-- Like https://hackage.haskell.org/package/ghc-prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `io` operations. -/
constant io.real_world : Type
-- TODO: make opaque
@[irreducible, derive monad]
def io : Type → Type := state io.real_world

@[extern "lean_io_unsafe"]
meta constant unsafe_io {α : Type} (fn : io α) : α

@[extern 4 "lean_io_timeit"]
constant timeit {α : Type} (msg : @& string) (fn : io α) : io α

@[extern 4 "lean_io_allocprof"]
constant allocprof {α : Type} (msg : @& string) (fn : io α) : io α

abbreviation monad_io (m : Type → Type) := has_monad_lift_t io m

-- TODO: make opaque
-- In the future, we may want to give more concrete data
-- like in https://doc.rust-lang.org/std/io/enum.ErrorKind.html
@[irreducible, derive has_to_string]
def io.error := string

section
local attribute [reducible] io.error
instance : inhabited io.error :=
⟨""⟩
end

-- The `io` primitives can also be used with [monad_except string m]
-- via this error conversion
instance : has_lift io.error string :=
⟨to_string⟩

/-- 'io with errors'. A useful default monad stack to use for operations
    in the `io` namespace if there is no need for additional layers or
    a more specific error type than `io.error`. -/
abbreviation eio := except_t io.error io

namespace io

section
local attribute [reducible] io
def lazy_pure {α : Type} (fn : unit → α) : io α :=
λ w, (fn (), w)
end

inductive fs.mode
| read | write | read_write | append
constant fs.handle : Type

namespace prim
open fs

def iterate_aux {α β : Type} (f : α → io (sum α β)) : (α → io β) → (α → io β)
| rec a :=
  do v ← f a,
  match v with
  | sum.inl a := rec a
  | sum.inr b := pure b

instance io_inhabited {β : Type} [inhabited β] : inhabited (io β) :=
⟨pure (default β)⟩

@[specialize] def iterate {α β : Type} [inhabited β] (a : α) (f : α → io (sum α β)) : io β :=
fix (iterate_aux f) a

instance {ε α : Type} [inhabited ε] : inhabited (except ε α) :=
⟨except.error (default ε)⟩

@[specialize] def iterate_eio {ε α β : Type} [inhabited ε] (a : α) (f : α → except_t ε io (sum α β)) : except_t ε io β :=
iterate a $ λ r, do
  r ← (f r).run,
  match r with
  | except.ok (sum.inl r) := pure (sum.inl r)
  | except.ok (sum.inr r) := pure (sum.inr (except.ok r))
  | except.error e        := pure (sum.inr (except.error e))

@[extern 2 "lean_io_prim_put_str"]
constant put_str (s: @& string) : eio unit
@[extern 1 "lean_io_prim_get_line"]
constant get_line : eio string
@[extern 4 "lean_io_prim_handle_mk"]
constant handle.mk (s : @& string) (m : mode) (bin : bool := ff) : eio handle
@[extern 2 "lean_io_prim_handle_is_eof"]
constant handle.is_eof (h : @& handle) : eio bool
@[extern 2 "lean_io_prim_handle_flush"]
constant handle.flush (h : @& handle) : eio unit
@[extern 2 "lean_io_prim_handle_close"]
constant handle.close (h : @& handle) : eio unit
-- TODO: replace `string` with byte buffer
-- constant handle.read : handle → nat → eio string
-- constant handle.write : handle → string → eio unit
@[extern 2 "lean_io_prim_handle_get_line"]
constant handle.get_line (h : @& handle) : eio string

@[inline] def lift_eio {m : Type → Type} {ε α : Type} [monad_io m] [monad_except ε m] [has_lift_t io.error ε] [monad m]
  (x : eio α) : m α :=
do e : except io.error α ← monad_lift (except_t.run x), -- uses [monad_io m] instance
   monad_except.lift_except e                           -- uses [monad_except ε m] [has_lift_t io.error ε] instances
end prim

section
variables {m : Type → Type} {ε : Type} [monad_io m] [monad_except ε m] [has_lift_t io.error ε] [monad m]

private def put_str : string → m unit :=
prim.lift_eio ∘ prim.put_str

def print {α} [has_to_string α] (s : α) : m unit :=
put_str ∘ to_string $ s

def println {α} [has_to_string α] (s : α) : m unit :=
print s *> put_str "\n"
end

namespace fs
variables {m : Type → Type} {ε : Type} [monad_io m] [monad_except ε m] [has_lift_t io.error ε] [monad m]

def handle.mk (s : string) (mode : mode) (bin : bool := ff) : m handle := prim.lift_eio (prim.handle.mk s mode bin)
def handle.is_eof : handle → m bool := prim.lift_eio ∘ prim.handle.is_eof
def handle.flush : handle → m unit := prim.lift_eio ∘ prim.handle.flush
def handle.close : handle → m unit := prim.lift_eio ∘ prim.handle.flush
-- def handle.read (h : handle) (bytes : nat) : m string := prim.lift_eio (prim.handle.read h bytes)
-- def handle.write (h : handle) (s : string) : m unit := prim.lift_eio (prim.handle.write h s)
def handle.get_line : handle → m string := prim.lift_eio ∘ prim.handle.get_line

/-
def get_char (h : handle) : m char :=
do b ← h.read 1,
   if b.is_empty then fail "get_char failed"
   else pure b.mk_iterator.curr
-/

-- def handle.put_char (h : handle) (c : char) : m unit :=
-- h.write (to_string c)

-- def handle.put_str (h : handle) (s : string) : m unit :=
-- h.write s

-- def handle.put_str_ln (h : handle) (s : string) : m unit :=
-- h.put_str s *> h.put_str "\n"

def handle.read_to_end (h : handle) : m string :=
prim.lift_eio $ prim.iterate_eio "" $ λ r, do
  done ← h.is_eof,
  if done
  then pure (sum.inr r) -- stop
  else do
    -- HACK: use less efficient `get_line` while `read` is broken
    c ← h.get_line,
    pure $ sum.inl (r ++ c) -- continue

def read_file (fname : string) (bin := ff) : m string :=
do h ← handle.mk fname mode.read bin,
   r ← h.read_to_end,
   h.close,
   pure r

-- def write_file (fname : string) (data : string) (bin := ff) : m unit :=
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
monad_io_process.child io_core

def child.stdin : child → handle :=
monad_io_process.stdin

def child.stdout : child → handle :=
monad_io_process.stdout

def child.stderr : child → handle :=
monad_io_process.stderr

def spawn (p : io.process.spawn_args) : io child :=
monad_io_process.spawn io_core p

def wait (c : child) : io nat :=
monad_io_process.wait c

end proc
-/
end io

/-
/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `string` which is then returned. -/
def io.cmd (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  s ← io.fs.read_to_end child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  if exitv ≠ 0 then io.fail $ "process exited with status " ++ repr exitv else pure (),
  pure s
-/

universe u

@[inline] def from_eio (x : eio unit) : io unit :=
x.run *> pure ()

def io.println' (x : string) : io unit :=
from_eio $ io.println x

/-- Typeclass used for presenting the output of an `#eval` command. -/
class has_eval (α : Type u) :=
(eval : α → io unit)

instance has_repr.has_eval {α : Type u} [has_repr α] : has_eval α :=
⟨λ a, io.println' (repr a)⟩

instance io.has_eval {α : Type} [has_eval α] : has_eval (io α) :=
⟨λ x, do a ← x, has_eval.eval a⟩

-- special case: do not print `()`
instance io_unit.has_eval : has_eval (io unit) :=
⟨λ x, x⟩

instance eio.has_eval {ε α : Type} [has_to_string ε] [has_eval α] : has_eval (except_t ε io α) :=
⟨λ x, do
   e : except ε α ← x.run,
   match e with
   | except.ok a    := has_eval.eval a
   | except.error e := io.println' ("Error: " ++ to_string e)⟩

-- special case: do not print `()`
instance eio_unit.has_eval {ε : Type} [has_to_string ε] : has_eval (except_t ε io unit) :=
⟨λ x, do
   e : except ε unit ← monad_lift $ x.run,
   match e with
   | except.ok _    := pure ()
   | except.error e := io.println' ("Error: " ++ to_string e)⟩

/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.estate init.data.string.basic init.fix

/-- Like https://hackage.haskell.org/package/ghc-prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `io` operations. -/
constant io.real_world : Type := unit

/- TODO(Leo): mark it as an opaque definition. Reason: prevent
   functions defined in other modules from accessing `io.real_world`.
   We don't want action such as
   ```
   def get_world : io (io.real_world) := get
   ```
-/
@[derive monad monad_except]
def eio (ε : Type) : Type → Type := estate ε io.real_world

instance {ε : Type} {α : Type} [inhabited ε] : inhabited (eio ε α) :=
infer_instance_as (inhabited (estate ε io.real_world α))

/-
In the future, we may want to give more concrete data
like in https://doc.rust-lang.org/std/io/enum.ErrorKind.html
-/
@[derive has_to_string inhabited]
def io.error := string

abbrev io : Type → Type := eio io.error

@[derive monad monad_except]
def init_io : Type → Type := estate io.error io.real_world

instance {α : Type} : inhabited (init_io α) :=
infer_instance_as (inhabited (estate io.error io.real_world α))

@[extern "lean_io_unsafe"]
constant unsafe_io {α : Type} (fn : io α) : option α := default _

@[extern 4 "lean_io_timeit"]
constant timeit {α : Type} (msg : @& string) (fn : io α) : io α := default _

@[extern 4 "lean_io_allocprof"]
constant allocprof {α : Type} (msg : @& string) (fn : io α) : io α := default _

abbrev monad_io (m : Type → Type) := has_monad_lift_t io m

def io_of_except {ε α : Type} [has_to_string ε] (e : except ε α) : io α :=
match e with
| except.ok a    := pure a
| except.error e := throw $ to_string e

namespace io

def lazy_pure {α : Type} (fn : unit → α) : io α :=
pure (fn ())

inductive fs.mode
| read | write | read_write | append

constant fs.handle : Type := unit

namespace prim
open fs

def iterate_aux {α β : Type} (f : α → io (sum α β)) : (α → io β) → (α → io β)
| rec a :=
  do v ← f a,
  match v with
  | sum.inl a := rec a
  | sum.inr b := pure b

@[specialize] def iterate {α β : Type} (a : α) (f : α → io (sum α β)) : io β :=
fix_core (λ _, throw "deep recursion") (iterate_aux f) a

instance {ε α : Type} [inhabited ε] : inhabited (except ε α) :=
⟨except.error (default ε)⟩

@[extern 2 "lean_io_prim_put_str"]
constant put_str (s: @& string) : io unit := default _
@[extern 1 "lean_io_prim_get_line"]
constant get_line : io string := default _
@[extern 4 "lean_io_prim_handle_mk"]
constant handle.mk (s : @& string) (m : mode) (bin : bool := ff) : io handle := default _
@[extern 2 "lean_io_prim_handle_is_eof"]
constant handle.is_eof (h : @& handle) : io bool := default _
@[extern 2 "lean_io_prim_handle_flush"]
constant handle.flush (h : @& handle) : io unit := default _
@[extern 2 "lean_io_prim_handle_close"]
constant handle.close (h : @& handle) : io unit := default _
-- TODO: replace `string` with byte buffer
-- constant handle.read : handle → nat → eio string
-- constant handle.write : handle → string → eio unit
@[extern 2 "lean_io_prim_handle_get_line"]
constant handle.get_line (h : @& handle) : io string := default _

@[inline] def lift_io {m : Type → Type} {α : Type} [monad_io m] (x : io α) : m α :=
monad_lift x
end prim

section
variables {m : Type → Type} [monad m] [monad_io m]

private def put_str : string → m unit :=
prim.lift_io ∘ prim.put_str

def print {α} [has_to_string α] (s : α) : m unit :=
put_str ∘ to_string $ s

def println {α} [has_to_string α] (s : α) : m unit :=
print s *> put_str "\n"
end

namespace fs
variables {m : Type → Type} [monad m] [monad_io m]

def handle.mk (s : string) (mode : mode) (bin : bool := ff) : m handle := prim.lift_io (prim.handle.mk s mode bin)
def handle.is_eof : handle → m bool := prim.lift_io ∘ prim.handle.is_eof
def handle.flush : handle → m unit := prim.lift_io ∘ prim.handle.flush
def handle.close : handle → m unit := prim.lift_io ∘ prim.handle.flush
-- def handle.read (h : handle) (bytes : nat) : m string := prim.lift_eio (prim.handle.read h bytes)
-- def handle.write (h : handle) (s : string) : m unit := prim.lift_eio (prim.handle.write h s)
def handle.get_line : handle → m string := prim.lift_io ∘ prim.handle.get_line

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
prim.lift_io $ prim.iterate "" $ λ r, do
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


/- References -/
constant ref (α : Type) : Type := unit

namespace prim
@[extern 3 cpp inline "lean::io_mk_ref(#2, #3)"]
constant mk_ref {α : Type} (a : α) : io (ref α)                := default _
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
variables {m : Type → Type} [monad m] [monad_io m]
@[inline] def mk_ref {α : Type} (a : α) : m (ref α) :=  prim.lift_io (prim.mk_ref a)
@[inline] def ref.read {α : Type} (r : ref α) : m α := prim.lift_io (prim.ref.read r)
@[inline] def ref.write {α : Type} (r : ref α) (a : α) : m unit := prim.lift_io (prim.ref.write r a)
@[inline] def ref.swap {α : Type} (r : ref α) (a : α) : m α := prim.lift_io (prim.ref.swap r a)
@[inline] def ref.reset {α : Type} (r : ref α) : m unit := prim.lift_io (prim.ref.reset r)
@[inline] def ref.modify {α : Type} (r : ref α) (f : α → α) : m unit :=
do v ← ref.read r,
   ref.reset r,
   ref.write r (f v)
end
end io

section init_io
@[extern 3 cpp inline "lean::io_mk_ref(#2, #3)"]
constant mk_global_ref {α : Type} (a : α) : init_io (io.ref α) := default _
end init_io

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

/-- Typeclass used for presenting the output of an `#eval` command. -/
class has_eval (α : Type u) :=
(eval : α → io unit)

instance has_repr.has_eval {α : Type u} [has_repr α] : has_eval α :=
⟨λ a, io.println (repr a)⟩

instance io.has_eval {α : Type} [has_eval α] : has_eval (io α) :=
⟨λ x, do a ← x, has_eval.eval a⟩

-- special case: do not print `()`
instance io_unit.has_eval : has_eval (io unit) :=
⟨λ x, x⟩

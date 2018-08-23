/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/

prelude
import init.control.state init.control.except init.data.string.basic init.control.coroutine
import init.meta.tactic

/-- Like https://hackage.haskell.org/package/ghc-prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `io` operations. -/
constant io.real_world : Type
-- TODO: make opaque
@[irreducible, derive monad]
def io : Type → Type := state io.real_world

abbreviation monad_io (m : Type → Type) := has_monad_lift_t io m

-- TODO: make opaque
-- In the future, we may want to give more concrete data
-- like in https://doc.rust-lang.org/std/io/enum.ErrorKind.html
@[irreducible, derive has_to_string]
def io.error := string

-- The `io` primitives can also be used with [monad_except string m]
-- via this error conversion
instance : has_lift io.error string :=
⟨to_string⟩

/-- 'io with errors'. A useful default monad stack to use for operations
    in the `io` namespace if there is no need for additional layers or
    a more specific error type than `io.error`. -/
abbreviation eio := except_t io.error io

namespace io

constant cmdline_args : io (list string)

inductive fs.mode
| read | write | read_write | append
constant fs.handle : Type

namespace prim
open fs

constant iterate {α β : Type} : α → (α → io (sum α β)) → io β

def iterate_eio {α β : Type} (a : α) (f : α → eio (sum α β)) : eio β :=
except_t.mk $ iterate a $ λ r, do
  r ← (f r).run,
  match r with
  | except.ok (sum.inl r) := pure (sum.inl r)
  | except.ok (sum.inr r) := pure (sum.inr (except.ok r))
  | except.error e        := pure (sum.inr (except.error e))

constant put_str : string → eio unit
constant get_line : eio string
constant handle.mk (s : string) (m : mode) (bin : bool := ff) : eio handle
constant handle.is_eof : handle → eio bool
constant handle.flush : handle → eio unit
constant handle.close : handle → eio unit
-- TODO: replace `string` with byte buffer
--constant handle.read : handle → nat → eio string
constant handle.write : handle → string → eio unit
constant handle.get_line : handle → eio string

def lift_eio {m : Type → Type} {ε α : Type} [monad_io m] [monad_except ε m] [has_lift_t io.error ε] [monad m]
  (x : eio α) : m α :=
do e : except io.error α ← monad_lift x.run, -- uses [monad_io m] instance
   monad_except.lift_except e                -- uses [monad_except ε m] [has_lift_t io.error ε] instances

end prim

section
variables {m : Type → Type} {ε : Type} [monad_io m] [monad_except ε m] [has_lift_t io.error ε] [monad m]

private def put_str : string → m unit :=
prim.lift_eio ∘ prim.put_str

def print {α} [has_to_string α] (s : α) : m unit :=
put_str ∘ to_string $ s

def println {α} [has_to_string α] (s : α) : m unit :=
print s >> put_str "\n"
end

namespace fs
variables {m : Type → Type} {ε : Type} [monad_io m] [monad_except ε m] [has_lift_t io.error ε] [monad m]

def handle.mk (s : string) (mode : mode) (bin : bool := ff) : m handle := prim.lift_eio (prim.handle.mk s mode bin)
def handle.is_eof : handle → m bool := prim.lift_eio ∘ prim.handle.is_eof
def handle.flush : handle → m unit := prim.lift_eio ∘ prim.handle.flush
def handle.close : handle → m unit := prim.lift_eio ∘ prim.handle.flush
--def handle.read (h : handle) (bytes : nat) : m string := prim.lift_eio (prim.handle.read h bytes)
def handle.write (h : handle) (s : string) : m unit := prim.lift_eio (prim.handle.write h s)
def handle.get_line : handle → m string := prim.lift_eio ∘ prim.handle.get_line

/-
def get_char (h : handle) : m char :=
do b ← h.read 1,
   if b.is_empty then fail "get_char failed"
   else return b.mk_iterator.curr
-/

def handle.put_char (h : handle) (c : char) : m unit :=
h.write (to_string c)

def handle.put_str (h : handle) (s : string) : m unit :=
h.write s

def handle.put_str_ln (h : handle) (s : string) : m unit :=
h.put_str s >> h.put_str "\n"

def handle.read_to_end (h : handle) : m string :=
prim.lift_eio $ prim.iterate_eio "" $ λ r, do
  done ← h.is_eof,
  if done
  then return (sum.inr r) -- stop
  else do
    -- HACK: use less efficient `get_line` while `read` is broken
    c ← h.get_line,
    return $ sum.inl (r ++ c) -- continue

def read_file (fname : string) (bin := ff) : m string :=
do h ← handle.mk fname mode.read bin,
   r ← h.read_to_end,
   h.close,
   return r

def write_file (fname : string) (data : string) (bin := ff) : m unit :=
do h ← handle.mk fname mode.write bin,
   h.write data,
   h.close

end fs

constant stdin : io fs.handle
constant stderr : io fs.handle
constant stdout : io fs.handle

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

meta constant format.print_using : format → options → io unit

meta definition format.print (fmt : format) : io unit :=
format.print_using fmt options.mk

meta definition pp_using {α : Type} [has_to_format α] (a : α) (o : options) : io unit :=
format.print_using (to_fmt a) o

meta definition pp {α : Type} [has_to_format α] (a : α) : io unit :=
format.print (to_fmt a)

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
  return s
-/

/--
This is the "back door" into the `io` monad, allowing IO computation to be performed during tactic execution.
For this to be safe, the IO computation should be ideally free of side effects and independent of its environment.
This primitive is used to invoke external tools (e.g., SAT and SMT solvers) from a tactic.

IMPORTANT: this primitive can be used to implement `unsafe_perform_io {α : Type} : io α → option α`
or `unsafe_perform_io {α : Type} [inhabited α] : io α → α`. This can be accomplished by executing
the resulting tactic using an empty `tactic_state` (we have `tactic_state.mk_empty`).
If `unsafe_perform_io` is defined, and used to perform side-effects, users need to take the following
precautions:

- Use `@[noinline]` attribute in any function to invokes `tactic.unsafe_perform_io`.
  Reason: if the call is inlined, the IO may be performed more than once.

- Set `set_option compiler.cse false` before any function that invokes `tactic.unsafe_perform_io`.
  This option disables common subexpression elimination. Common subexpression elimination
  might combine two side effects that were meant to be separate.

TODO[Leo]: add `[noinline]` attribute and option `compiler.cse`.
-/
meta constant tactic.unsafe_run_io {α : Type} : io α → tactic α

/--
   Execute the given tactic with a tactic_state object that contains:
   - The current environment in the virtual machine.
   - The current set of options in the virtual machine.
   - Empty metavariable and local contexts.
   - One single goal of the form `⊢ true`.
   This action is mainly useful for writing tactics that inspect
   the environment. -/
meta constant io.run_tactic {α : Type} (a : tactic α) : except_t format io α


universe u

/-- Typeclass used for presenting the output of an `#eval` command. -/
meta class has_eval (α : Type u) :=
(eval : α → tactic unit)

meta instance has_repr.has_eval {α : Type u} [has_repr α] : has_eval α :=
⟨tactic.trace ∘ repr⟩

meta instance tactic.has_eval {α : Type} [has_eval α] : has_eval (tactic α) :=
⟨(>>= has_eval.eval)⟩

-- special case: do not print `()`
meta instance tactic_unit.has_eval : has_eval (tactic unit) :=
⟨id⟩

meta instance io.has_eval {α : Type} [has_eval α] : has_eval (io α) :=
⟨λ x, tactic.unsafe_run_io x >>= has_eval.eval⟩

-- special case: do not print `()`
meta instance io_unit.has_eval : has_eval (io unit) :=
⟨tactic.unsafe_run_io⟩

meta instance eio.has_eval {ε α : Type} [has_to_format ε] [has_eval α] : has_eval (except_t ε io α) :=
⟨λ x, do
  r ← tactic.unsafe_run_io x.run,
  match r with
  | except.error e := tactic.fail e
  | except.ok a    := has_eval.eval a⟩

-- special case: do not print `()`
meta instance eio_unit.has_eval {ε : Type} [has_to_format ε] : has_eval (except_t ε io unit) :=
⟨λ x, do
  r ← tactic.unsafe_run_io x.run,
  match r with
  | except.error e := tactic.fail e
  | except.ok a    := pure ()⟩

local attribute [reducible] io
/-- A variant of `coroutine` on top of `io` -/
inductive coroutine_io (α δ β: Type) : Type
| mk    {} : (α → io (coroutine_result_core.{0 0 0} coroutine_io α δ β)) → coroutine_io

abbreviation coroutine_result_io (α δ β: Type) : Type :=
coroutine_result_core.{0 0 0} (coroutine_io α δ β) α δ β

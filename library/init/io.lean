/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.state init.control.except init.data.string.basic init.control.coroutine

/-- Like https://hackage.haskell.org/package/ghc-prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld.
    Makes sure we never reorder `io` operations. -/
constant io.real_world : Type
-- TODO: make opaque
@[irreducible, derive monad]
def io : Type → Type := state io.real_world

@[extern "lean_io_unsafe"]
meta constant unsafe_io {α : Type} (fn : io α) : α

@[extern 4 "lean_io_timeit"]
constant timeit {α : Type} (msg : string) (fn : io α) : io α

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

/- TODO(Leo): mark as an opaque primitive.
   This function does not necessarily terminate, and is not marked as `meta`.
   We ensure that the resulting system is sound by marking it as an "opaque primitive".
   Thus, users cannot "view" its implementation. It is essentially an opaque
   constant that is useful for writing programs in Lean.
   In previous versions, `iterate` was indeed a `constant` instead of a definition.
   We changed it because the Lean compiler could not specialize `iterate` applications
   since there was no code to be specialized. -/
@[specialize] def iterate {α β : Type} : α → (α → io (sum α β)) → io β
| a f :=
  do v ← f a,
  match v with
  | sum.inl a' := iterate a' f
  | sum.inr b  := pure b

@[specialize] def iterate_eio {ε α β : Type} (a : α) (f : α → except_t ε io (sum α β)) : except_t ε io β :=
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
meta class has_eval (α : Type u) :=
(eval : α → io unit)

meta instance has_repr.has_eval {α : Type u} [has_repr α] : has_eval α :=
⟨λ a, io.println' (repr a)⟩

meta instance io.has_eval {α : Type} [has_eval α] : has_eval (io α) :=
⟨λ x, do a ← x, has_eval.eval a⟩

-- special case: do not print `()`
meta instance io_unit.has_eval : has_eval (io unit) :=
⟨λ x, x⟩

meta instance eio.has_eval {ε α : Type} [has_to_string ε] [has_eval α] : has_eval (except_t ε io α) :=
⟨λ x, do
   e : except ε α ← x.run,
   match e with
   | except.ok a    := has_eval.eval a
   | except.error e := io.println' ("Error: " ++ to_string e)⟩

-- special case: do not print `()`
meta instance eio_unit.has_eval {ε : Type} [has_to_string ε] : has_eval (except_t ε io unit) :=
⟨λ x, do
   e : except ε unit ← monad_lift $ x.run,
   match e with
   | except.ok _    := pure ()
   | except.error e := io.println' ("Error: " ++ to_string e)⟩

local attribute [reducible] io
/-- A variant of `coroutine` on top of `io`
    TODO(Leo): replace `state_t io.real_world id` with `io` as soon as we fix inductive_cmd
-/
inductive coroutine_io (α δ β: Type) : Type
| mk    {} : (α → io.real_world → (coroutine_result_core.{0 0 0} coroutine_io α δ β) × io.real_world) → coroutine_io

abbreviation coroutine_result_io (α δ β: Type) : Type :=
coroutine_result_core.{0 0 0} (coroutine_io α δ β) α δ β

/-! A variant of `coroutine` on top of `io`. Implementation. -/

universes v w r s

namespace coroutine_io
variables {α δ β γ : Type}

@[inline] def mk_st {α δ β: Type} (k : α → state_t io.real_world id (coroutine_result_io α δ β)) : coroutine_io α δ β :=
mk k

export coroutine_result_core (done yielded)

/-- `resume c a` resumes/invokes the coroutine_io `c` with input `a`. -/
@[inline] def resume : coroutine_io α δ β → α → io (coroutine_result_io α δ β)
| (mk k) a := k a

@[inline] protected def pure (b : β) : coroutine_io α δ β :=
mk_st $ λ _, pure $ done b

/-- Read the input argument passed to the coroutine.
    Remark: should we use a different name? I added an instance [monad_reader] later. -/
@[inline] protected def read : coroutine_io α δ α :=
mk_st $ λ a, pure $ done a

/-- Return the control to the invoker with result `d` -/
@[inline] protected def yield (d : δ) : coroutine_io α δ punit :=
mk_st $ λ (a : α), pure $ yielded d (coroutine_io.pure ⟨⟩)

/-
TODO(Leo): following relations have been commented because Lean4 is currently
accepting non-terminating programs.

/-- Auxiliary relation for showing that bind/pipe terminate -/
inductive direct_subcoroutine_io : coroutine_io α δ β → coroutine_io α δ β → Prop
| mk : ∀ (k : α → coroutine_result α δ β) (a : α) (d : δ) (c : coroutine_io α δ β), k a = yielded d c → direct_subcoroutine_io c (mk k)

theorem direct_subcoroutine_wf : well_founded (@direct_subcoroutine_io α δ β) :=
begin
  constructor, intro c,
  apply @coroutine.ind _ _ _
          (λ c, acc direct_subcoroutine_io c)
          (λ r, ∀ (d : δ) (c : coroutine_io α δ β), r = yielded d c → acc direct_subcoroutine_io c),
  { intros k ih, dsimp at ih, constructor, intros c' h, cases h, apply ih h_a h_d, assumption },
  { intros, contradiction },
  { intros d c ih d₁ c₁ heq, injection heq, subst c, assumption }
end

/-- Transitive closure of direct_subcoroutine. It is not used here, but may be useful when defining
    more complex procedures. -/
def subcoroutine_io : coroutine_io α δ β → coroutine_io α δ β → Prop :=
tc direct_subcoroutine_io

theorem subcoroutine_wf : well_founded (@subcoroutine_io α δ β) :=
tc.wf direct_subcoroutine_wf

-- Local instances for proving termination by well founded relation

def bind_wf_inst : has_well_founded (Σ' a : coroutine_io α δ β, (β → coroutine_io α δ γ)) :=
{ r  := psigma.lex direct_subcoroutine_io (λ _, empty_relation),
  wf := psigma.lex_wf direct_subcoroutine_wf (λ _, empty_wf) }

def pipe_wf_inst : has_well_founded (Σ' a : coroutine_io α δ β, coroutine_io δ γ β) :=
{ r  := psigma.lex direct_subcoroutine_io (λ _, empty_relation),
  wf := psigma.lex_wf direct_subcoroutine_wf (λ _, empty_wf) }

local attribute [instance] wf_inst₁ wf_inst₂

open well_founded_tactics

-/

protected def bind : coroutine_io α δ β → (β → coroutine_io α δ γ) → coroutine_io α δ γ
| (mk k) f := mk_st $ λ a, k a >>= λ r,
    match r, rfl : ∀ (n : _), n = r → _ with
    | done b, _      := coroutine_io.resume (f b) a
    | yielded d c, h :=
      -- have direct_subcoroutine_io c (mk k), { apply direct_subcoroutine.mk k a d, rw h },
      pure $ yielded d (bind c f)
--  using_well_founded { dec_tac := unfold_wf_rel *> process_lex (tactic.assumption) }

def pipe : coroutine_io α δ β → coroutine_io δ γ β → coroutine_io α γ β
| (mk k₁) (mk k₂) := mk_st $ λ a, do
  r ← k₁ a,
  match r, rfl : ∀ (n : _), n = r → _ with
  | done b, h        := pure (done b)
  | yielded d k₁', h := do
    r ← k₂ d,
    pure $ match r with
    | done b        := done b
    | yielded r k₂' :=
      -- have direct_subcoroutine_io k₁' (mk k₁), { apply direct_subcoroutine.mk k₁ a d, rw h },
      yielded r (pipe k₁' k₂')
-- using_well_founded { dec_tac := unfold_wf_rel *> process_lex (tactic.assumption) }

instance : monad (coroutine_io α δ) :=
{ pure := @coroutine_io.pure _ _,
  bind := @coroutine_io.bind _ _ }

instance : monad_reader α (coroutine_io α δ) :=
{ read := @coroutine_io.read _ _ }

instance (α δ : Type) : monad_coroutine α δ (coroutine_io α δ) :=
{ yield  := coroutine_io.yield }

instance : monad_io (coroutine_io α δ) :=
{ monad_lift := λ _ x, mk_st (λ _, done <$> x) }

end coroutine_io

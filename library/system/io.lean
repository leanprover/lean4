/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
import system.io_interface

/- The following constants have a builtin implementation -/
constant io_core : Type → Type → Type

/- Auxiliary definition used in the builtin implementation of monad_io_random_impl -/
def io_rand_nat : std_gen → nat → nat → nat × std_gen :=
rand_nat

@[instance] constant monad_io_impl             : monad_io io_core
@[instance] constant monad_io_terminal_impl    : monad_io_terminal io_core
@[instance] constant monad_io_file_system_impl : monad_io_file_system io_core
@[instance] constant monad_io_environment_impl : monad_io_environment io_core
@[instance] constant monad_io_process_impl     : monad_io_process io_core
@[instance] constant monad_io_random_impl      : monad_io_random io_core

instance io_core_is_monad (e : Type) : monad (io_core e) :=
monad_io_is_monad io_core e

instance io_core_is_monad_fail : monad_fail (io_core io.error) :=
monad_io_is_monad_fail io_core

instance io_core_is_alternative : alternative (io_core io.error) :=
monad_io_is_alternative io_core

@[reducible] def io (α : Type) :=
io_core io.error α

namespace io
/- Remark: the following definitions can be generalized and defined for any (m : Type -> Type -> Type)
   that implements the required type classes. However, the generalized versions are very inconvenient to use,
   (example: `#eval io.put_str "hello world"` does not work because we don't have enough information to infer `m`.).
-/
def iterate {e α} (a : α) (f : α → io_core e (option α)) : io_core e α :=
monad_io.iterate e α a f

def forever {e} (a : io_core e unit) : io_core e unit :=
iterate () $ λ _, a >> return (some ())

-- TODO(Leo): delete after we merge #1881
def catch {e₁ e₂ α} (a : io_core e₁ α) (b : e₁ → io_core e₂ α) : io_core e₂ α :=
monad_io.catch e₁ e₂ α a b

def finally {α e} (a : io_core e α) (cleanup : io_core e unit) : io_core e α := do
res ← catch (sum.inr <$> a) (return ∘ sum.inl),
cleanup,
match res with
| sum.inr res := return res
| sum.inl error := monad_io.fail _ _ _ error
end

protected def fail {α : Type} (s : string) : io α :=
monad_io.fail io_core _ _ (io.error.other s)

def put_str : string → io unit :=
monad_io_terminal.put_str io_core

def put_str_ln (s : string) : io unit :=
put_str s >> put_str "\n"

def get_line : io string :=
monad_io_terminal.get_line io_core

def cmdline_args : io (list string) :=
return (monad_io_terminal.cmdline_args io_core)

def print {α} [has_to_string α] (s : α) : io unit :=
put_str ∘ to_string $ s

def print_ln {α} [has_to_string α] (s : α) : io unit :=
print s >> put_str "\n"

def handle : Type :=
monad_io.handle io_core

def mk_file_handle (s : string) (m : mode) (bin : bool := ff) : io handle :=
monad_io_file_system.mk_file_handle io_core s m bin

def stdin : io handle :=
monad_io_file_system.stdin io_core

def stderr : io handle :=
monad_io_file_system.stderr io_core

def stdout : io handle :=
monad_io_file_system.stdout io_core

namespace env

def get (env_var : string) : io (option string) :=
monad_io_environment.get_env io_core env_var

/-- get the current working directory -/
def get_cwd : io string :=
monad_io_environment.get_cwd io_core

/-- set the current working directory -/
def set_cwd (cwd : string) : io unit :=
monad_io_environment.set_cwd io_core cwd

end env

namespace fs
def is_eof : handle → io bool :=
monad_io_file_system.is_eof

def flush : handle → io unit :=
monad_io_file_system.flush

def close : handle → io unit :=
monad_io_file_system.close

def read : handle → nat → io char_buffer :=
monad_io_file_system.read

def write : handle → char_buffer → io unit :=
monad_io_file_system.write

def get_char (h : handle) : io char :=
do b ← read h 1,
   if h : b.size = 1 then return $ b.read ⟨0, h.symm ▸ zero_lt_one⟩
   else io.fail "get_char failed"

def get_line : handle → io char_buffer :=
monad_io_file_system.get_line

def put_char (h : handle) (c : char) : io unit :=
write h (mk_buffer.push_back c)

def put_str (h : handle) (s : string) : io unit :=
write h (mk_buffer.append_string s)

def put_str_ln (h : handle) (s : string) : io unit :=
put_str h s >> put_str h "\n"

def read_to_end (h : handle) : io char_buffer :=
iterate mk_buffer $ λ r,
  do done ← is_eof h,
    if done
    then return none
    else do
      c ← read h 1024,
      return $ some (r ++ c)

def read_file (s : string) (bin := ff) : io char_buffer :=
do h ← mk_file_handle s io.mode.read bin,
   read_to_end h

end fs

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

def set_rand_gen : std_gen → io unit :=
monad_io_random.set_rand_gen io_core

def rand (lo : nat := std_range.1) (hi : nat := std_range.2) : io nat :=
monad_io_random.rand io_core lo hi

end io

meta constant format.print_using : format → options → io unit

meta definition format.print (fmt : format) : io unit :=
format.print_using fmt options.mk

meta definition pp_using {α : Type} [has_to_format α] (a : α) (o : options) : io unit :=
format.print_using (to_fmt a) o

meta definition pp {α : Type} [has_to_format α] (a : α) : io unit :=
format.print (to_fmt a)

/-- Run the external process specified by `args`.

    The process will run to completion with its output captured by a pipe, and
    read into `string` which is then returned. -/
def io.cmd (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  buf ← io.fs.read_to_end child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string

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
meta constant io.run_tactic {α : Type} (a : tactic α) : io α

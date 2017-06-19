/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
import data.buffer

inductive io.error
| other     : string → io.error
| sys       : nat → io.error

structure io.terminal (m : Type → Type → Type) :=
(put_str     : string → m io.error unit)
(get_line    : m io.error string)
(cmdline_args : list string)

inductive io.mode
| read | write | read_write | append

structure io.file_system (handle : Type) (m : Type → Type → Type) :=
/- Remark: in Haskell, they also provide  (Maybe TextEncoding) and  NewlineMode -/
(mk_file_handle : string → io.mode → bool → m io.error handle)
(is_eof         : handle → m io.error bool)
(flush          : handle → m io.error unit)
(close          : handle → m io.error unit)
(read           : handle → nat → m io.error char_buffer)
(write          : handle → char_buffer → m io.error unit)
(get_line       : handle → m io.error char_buffer)
(stdin          : m io.error handle)
(stdout         : m io.error handle)
(stderr         : m io.error handle)

structure io.environment (m : Type → Type → Type) :=
(get_env : string → m io.error (option string))
-- we don't provide set_env as it is (thread-)unsafe (at least with glibc)

inductive io.process.stdio
| piped
| inherit
| null

structure io.process.spawn_args :=
/- Command name. -/
(cmd : string)
/- Arguments for the process -/
(args : list string := [])
/- Configuration for the process' stdin handle. -/
(stdin := stdio.inherit)
/- Configuration for the process' stdout handle. -/
(stdout := stdio.inherit)
/- Configuration for the process' stderr handle. -/
(stderr := stdio.inherit)
/- Working directory for the process. -/
(cwd : option string := none)
/- Environment variables for the process. -/
(env : list (string × option string) := [])

structure io.process (handle : Type) (m : Type → Type → Type) :=
(child : Type) (stdin : child → handle) (stdout : child → handle) (stderr : child → handle)
(spawn : io.process.spawn_args → m io.error child)
(wait : child → m io.error nat)

class io.interface :=
(m        : Type → Type → Type)
(monad    : Π e, monad (m e))
(catch    : Π e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α)
(fail     : Π e α, e → m e α)
(iterate  : Π e α, α → (α → m e (option α)) → m e α)
-- Primitive Types
(handle   : Type)
-- Interface Extensions
(term     : io.terminal m)
(fs       : io.file_system handle m)
(process  : io.process handle m)
(env      : io.environment m)

variable [ioi : io.interface]
include ioi

def io_core (e : Type) (α : Type) :=
io.interface.m e α

@[reducible] def io (α : Type) :=
io_core io.error α

instance io_core_is_monad (e : Type) : monad (io_core e) :=
io.interface.monad e

protected def io.fail {α : Type} (s : string) : io α :=
io.interface.fail io.error α (io.error.other s)

instance : monad_fail io :=
{ io_core_is_monad io.error with
  fail := @io.fail _ }

namespace io
def iterate {e α} (a : α) (f : α → io_core e (option α)) : io_core e α :=
interface.iterate e α a f

def forever {e} (a : io_core e unit) : io_core e unit :=
iterate () $ λ _, a >> return (some ())

def catch {e₁ e₂ α} (a : io_core e₁ α) (b : e₁ → io_core e₂ α) : io_core e₂ α :=
interface.catch e₁ e₂ α a b

def finally {α e} (a : io_core e α) (cleanup : io_core e unit) : io_core e α := do
res ← catch (sum.inr <$> a) (return ∘ sum.inl),
cleanup,
match res with
| sum.inr res := return res
| sum.inl error := io.interface.fail _ _ error
end

instance : alternative io :=
{ interface.monad _ with
  orelse := λ _ a b, catch a (λ _, b),
  failure := λ _, io.fail "failure" }

def put_str : string → io unit :=
interface.term.put_str

def put_str_ln (s : string) : io unit :=
put_str s >> put_str "\n"

def get_line : io string :=
interface.term.get_line

def cmdline_args : io (list string) :=
return interface.term.cmdline_args

def print {α} [has_to_string α] (s : α) : io unit :=
put_str ∘ to_string $ s

def print_ln {α} [has_to_string α] (s : α) : io unit :=
print s >> put_str "\n"

def handle : Type :=
interface.handle

def mk_file_handle (s : string) (m : mode) (bin : bool := ff) : io handle :=
interface.fs.mk_file_handle s m bin

def stdin : io handle :=
interface.fs.stdin

def stderr : io handle :=
interface.fs.stderr

def stdout : io handle :=
interface.fs.stdout

namespace env

def get (env_var : string) : io (option string) :=
interface.env.get_env env_var

end env

namespace fs
def is_eof : handle → io bool :=
interface.fs.is_eof

def flush : handle → io unit :=
interface.fs.flush

def close : handle → io unit :=
interface.fs.close

def read : handle → nat → io char_buffer :=
interface.fs.read

def write : handle → char_buffer → io unit :=
interface.fs.write

def get_char (h : handle) : io char :=
do b ← read h 1,
   if h : b.size = 1 then return $ b.read ⟨0, h.symm ▸ zero_lt_one⟩
   else io.fail "get_char failed"

def get_line : handle → io char_buffer :=
interface.fs.get_line

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
def child : Type := interface.process.child
def child.stdin : child → handle := interface.process.stdin
def child.stdout : child → handle := interface.process.stdout
def child.stderr : child → handle := interface.process.stderr
def spawn (p : io.process.spawn_args) : io child := interface.process.spawn p
def wait (c : child) : io nat := interface.process.wait c
end proc

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
    read into `string` which is then returned.
-/
def io.cmd (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { args with stdout := io.process.stdio.piped },
  buf ← io.fs.read_to_end child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string

omit ioi
/-- Lift a monadic `io` action into the `tactic` monad. -/
meta constant tactic.run_io {α : Type} : (Π ioi : io.interface, @io ioi α) → tactic α

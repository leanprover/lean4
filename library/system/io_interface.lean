/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.buffer system.random

inductive io.error
| other     : string → io.error
| sys       : nat → io.error

inductive io.mode
| read | write | read_write | append

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

class monad_io (m : Type → Type → Type) :=
[monad    : Π e, monad (m e)]
-- TODO(Leo): use monad_except after it is merged
(catch    : Π e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α)
(fail     : Π e α, e → m e α)
(iterate  : Π e α, α → (α → m e (option α)) → m e α)
-- Primitive Types
(handle   : Type)

class monad_io_terminal (m : Type → Type → Type) :=
(put_str      : string → m io.error unit)
(get_line     : m io.error string)
(cmdline_args : list string)

open monad_io (handle)

class monad_io_file_system (m : Type → Type → Type) [monad_io m] :=
/- Remark: in Haskell, they also provide  (Maybe TextEncoding) and  NewlineMode -/
(mk_file_handle : string → io.mode → bool → m io.error (handle m))
(is_eof         : (handle m) → m io.error bool)
(flush          : (handle m) → m io.error unit)
(close          : (handle m) → m io.error unit)
(read           : (handle m) → nat → m io.error char_buffer)
(write          : (handle m) → char_buffer → m io.error unit)
(get_line       : (handle m) → m io.error char_buffer)
(stdin          : m io.error (handle m))
(stdout         : m io.error (handle m))
(stderr         : m io.error (handle m))

class monad_io_environment (m : Type → Type → Type) :=
(get_env : string → m io.error (option string))
-- we don't provide set_env as it is (thread-)unsafe (at least with glibc)
(get_cwd : m io.error string)
(set_cwd : string → m io.error unit)

class monad_io_process (m : Type → Type → Type) [monad_io m] :=
(child  : Type)
(stdin  : child → (handle m))
(stdout : child → (handle m))
(stderr : child → (handle m))
(spawn  : io.process.spawn_args → m io.error child)
(wait   : child → m io.error nat)

class monad_io_random (m : Type → Type → Type) :=
(set_rand_gen : std_gen → m io.error unit)
(rand         : nat → nat → m io.error nat)

instance monad_io_is_monad (m : Type → Type → Type) (e : Type) [monad_io m] : monad (m e) :=
monad_io.monad m e

instance monad_io_is_monad_fail (m : Type → Type → Type) [monad_io m] : monad_fail (m io.error) :=
{ fail := λ α s, monad_io.fail _ _ _ (io.error.other s) }

instance monad_io_is_alternative (m : Type → Type → Type) [monad_io m] : alternative (m io.error) :=
{ orelse  := λ α a b, monad_io.catch _ _ _ a (λ _, b),
  failure := λ α, monad_io.fail _ _ _ (io.error.other "failure") }

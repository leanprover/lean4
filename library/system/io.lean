/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
import data.buffer

inductive io.error_kind
| not_found | permission_denied | connection_refused
| connection_reset | connection_aborted | not_connected
| addr_in_use | addr_not_available | broken_pipe
| already_exists | would_block | invalid_input
| invalid_data | timeout | write_zero | interrupted
| unexpected_eof

inductive io.error
| other     : string → io.error
| sys       : nat → io.error
| primitive : io.error_kind → io.error

structure io.terminal (m : Type → Type → Type) :=
(put_str     : string → m io.error unit)
(get_line    : m io.error string)

inductive io.mode
| read | write | read_write | append

structure io.file_system (m : Type → Type → Type) :=
/- Remark: in Haskell, they also provide  (Maybe TextEncoding) and  NewlineMode -/
(handle         : Type)
(mk_file_handle : string → io.mode → bool → m io.error handle)
(file_size      : handle → m io.error nat)
(is_eof         : handle → m io.error bool)
(look_ahead     : handle → m io.error char)
(flush          : handle → m io.error unit)
(close          : handle → m io.error unit)
(read           : handle → nat → m io.error char_buffer)
(write          : handle → char_buffer → m io.error unit)
(get_line       : handle → m io.error char_buffer)

class io.interface :=
(m        : Type → Type → Type)
(return   : Π e α, α → m e α)
(bind     : Π e α β, m e α → (α → m e β) → m e β)
(catch    : Π e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α)
(fail     : Π e α, e → m e α)
(term     : io.terminal m)
(fs       : io.file_system m)

variable [io.interface]

def io_core (e : Type) (α : Type) :=
io.interface.m e α

@[reducible] def io (α : Type) :=
io_core io.error α

instance io_core_is_monad (e : Type) : monad (io_core e) :=
{ pure := io.interface.return e,
  bind := io.interface.bind e }

protected def io.fail (α : Type) (s : string) : io α :=
io.interface.fail io.error α (io.error.other s)

instance : monad_fail io :=
{ pure := io.interface.return io.error,
  bind := io.interface.bind io.error,
  fail := io.fail }

namespace io
def put_str : string → io unit :=
interface.term^.put_str

def put_str_ln (s : string) : io unit :=
put_str s >> put_str "\n"

def get_line : io string :=
interface.term^.get_line

def print {α} [has_to_string α] (s : α) : io unit :=
put_str ∘ to_string $ s

def print_ln {α} [has_to_string α] (s : α) : io unit :=
print s >> put_str "\n"

def handle : Type :=
interface.fs^.handle

def mk_file_handle (s : string) (m : mode) (bin : bool := ff) : io handle :=
interface.fs^.mk_file_handle s m bin

def pfail {α} (k : io.error_kind) : io α :=
interface.fail io.error α (io.error.primitive k)

namespace fs
def size : handle → io nat :=
interface.fs^.file_size

def is_eof : handle → io bool :=
interface.fs^.is_eof

def look_ahead : handle → io char :=
interface.fs^.look_ahead

def flush : handle → io unit :=
interface.fs^.flush

def close : handle → io unit :=
interface.fs^.close

def read : handle → nat → io char_buffer :=
interface.fs^.read

def write : handle → char_buffer → io unit :=
interface.fs^.write

def get_char (h : handle) : io char :=
do b ← read h 1,
   if h : b^.size = 1 then return $ b^.read ⟨0, h^.symm ▸ zero_lt_one⟩
   else pfail error_kind.unexpected_eof

def get_line : handle → io char_buffer :=
interface.fs^.get_line

def put_char (h : handle) (c : char) : io unit :=
do write h (mk_buffer^.push_back c)
end fs

def read_file (s : string) (bin := ff) : io char_buffer :=
do h  ← mk_file_handle s mode.read bin,
   sz ← fs.size h,
   fs.read h sz
end io

meta constant format.print_using [io.interface] : format → options → io unit

meta definition format.print (fmt : format) : io unit :=
format.print_using fmt options.mk

meta definition pp_using {α : Type} [has_to_format α] (a : α) (o : options) : io unit :=
format.print_using (to_fmt a) o

meta definition pp {α : Type} [has_to_format α] (a : α) : io unit :=
format.print (to_fmt a)

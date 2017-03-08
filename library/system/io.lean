/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
universe u
constant io : Type u → Type u
protected constant io.return : ∀ {α : Type u}, α → io α
protected constant io.bind   : ∀ {α β : Type u}, io α → (α → io β) → io β
protected constant io.map    : ∀ {α β : Type u}, (α → β) → io α → io β
constant io.put_str          : string → io unit
constant io.get_line         : io string

instance : monad io :=
{ pure := @io.return,
  bind := @io.bind,
  map  := @io.map }

namespace io
def put {α} [has_to_string α] (s : α) : io unit :=
put_str ∘ to_string $ s

def put_ln {α} [has_to_string α] (s : α) : io unit :=
put s >> put_str "\n"
end io

meta constant format.print_using : format → options → io unit

meta definition format.print (fmt : format) : io unit :=
format.print_using fmt options.mk

meta definition pp_using {α : Type} [has_to_format α] (a : α) (o : options) : io unit :=
format.print_using (to_fmt a) o

meta definition pp {α : Type} [has_to_format α] (a : α) : io unit :=
format.print (to_fmt a)

/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
constant {u} io : Type u → Type u
constant io.functor : functor io
constant io.monad   : monad io

attribute [instance] io.functor io.monad

constant put_str  : string → io unit
constant put_nat  : nat → io unit
constant get_line : io string

def put_str_ln {A} [has_to_string A] (s : A) : io unit :=
  put_str $ #"\n" :: (to_string s)

meta constant format.print_using : format → options → io unit

meta definition format.print (fmt : format) : io unit :=
format.print_using fmt options.mk

meta definition pp_using {α : Type} [has_to_format α] (a : α) (o : options) : io unit :=
format.print_using (to_fmt a) o

meta definition pp {α : Type} [has_to_format α] (a : α) : io unit :=
format.print (to_fmt a)

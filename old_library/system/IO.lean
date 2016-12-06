/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/

constant {u} IO : Type u → Type u
constant functorIO : functor IO
constant monadIO : monad IO

attribute [instance] functorIO monadIO

constant put_str : string → IO unit
constant put_nat : nat → IO unit
constant get_line : IO string

constant forever : IO unit -> IO unit

definition put_str_ln (x : string) : IO unit :=
  put_str ('\n' :: x)

definition print_str {A : Type} [str : has_to_string A] (a : A) : IO unit :=
   put_str_ln (to_string a)

meta_constant format.print_using : format → options → IO unit

meta_definition format.print (fmt : format) : IO unit :=
format.print_using fmt options.mk

meta_definition pp_using {A : Type} [has_to_format A] (a : A) (o : options) : IO unit :=
format.print_using (to_fmt a) o

meta_definition pp {A : Type} [has_to_format A] (a : A) : IO unit :=
format.print (to_fmt a)

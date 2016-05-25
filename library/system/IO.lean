/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch and Leonardo de Moura
-/
constant IO : Type → Type₁
constant functorIO : functor IO
constant monadIO : monad IO

attribute [instance] functorIO monadIO

constant put_str : string → IO unit
constant put_nat : nat → IO unit
constant get_line : IO string

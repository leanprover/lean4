/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.list.instances

instance string.has_decidable_eq : decidable_eq string :=
by tactic.mk_dec_eq_instance

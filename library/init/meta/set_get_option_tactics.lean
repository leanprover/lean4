/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
meta def set_bool_option (n : name) (v : bool) : tactic unit :=
do s ← read,
   write $ tactic_state.set_options s (options.set_bool (tactic_state.get_options s) n v)

meta def set_nat_option (n : name) (v : nat) : tactic unit :=
do s ← read,
   write $ tactic_state.set_options s (options.set_nat (tactic_state.get_options s) n v)

meta def set_string_option (n : name) (v : string) : tactic unit :=
do s ← read,
   write $ tactic_state.set_options s (options.set_string (tactic_state.get_options s) n v)

meta def get_bool_option (n : name) (default : bool) : tactic bool :=
do s ← read,
   return $ options.get_bool (tactic_state.get_options s) n default

meta def get_nat_option (n : name) (default : nat) : tactic nat :=
do s ← read,
   return $ options.get_nat (tactic_state.get_options s) n default

meta def get_string_option (n : name) (default : string) : tactic string :=
do s ← read,
   return $ options.get_string (tactic_state.get_options s) n default
end tactic

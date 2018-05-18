/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.data.rbmap init.lean.name
universe u

namespace lean

inductive option_value
| from_string (s : string)
| from_nat (u : nat)
| from_bool   (b : bool)

def options := rbmap name option_value name.has_lt_quick.lt

namespace options
variables (opts : options) (n : name)

def mk : options := mk_rbmap _ _ _

def get_string : option string :=
match opts.find n with
| some (option_value.from_string s) := some s
| _ := none

def get_nat : option nat :=
match opts.find n with
| some (option_value.from_nat u) := some u
| _ := none

def get_bool : option bool :=
match opts.find n with
| some (option_value.from_bool b) := some b
| _ := none

def set_string (s : string) : options :=
rbmap.insert opts n (option_value.from_string s)

def set_nat (u : nat) : options :=
rbmap.insert opts n (option_value.from_nat u)

def set_bool (b : bool) : options :=
rbmap.insert opts n (option_value.from_bool b)

end options
end lean

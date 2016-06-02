/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/- Reflect a C++ name object. The VM replaces it with the C++ implementation. -/
inductive name :=
| anonymous  : name
| mk_string  : string → name → name
| mk_numeral : unsigned → name → name

definition mk_str_name (n : name) (s : string) : name :=
name.mk_string s n

definition mk_num_name (n : name) (v : nat) : name :=
name.mk_numeral (unsigned.of_nat v) n

definition mk_simple_name [coercion] (s : string) : name :=
mk_str_name name.anonymous s

namespace name
infix ` <s> `:65 := mk_str_name
infix ` <n> `:65 := mk_num_name
end name

open name

definition name.to_string : name → string
| anonymous                := "[anonymous]"
| (mk_string s anonymous)  := s
| (mk_numeral v anonymous) := to_string v
| (mk_string s n)          := name.to_string n + "." + s
| (mk_numeral v n)         := name.to_string n + "." + to_string v

definition name.has_to_string [instance] : has_to_string name :=
has_to_string.mk name.to_string

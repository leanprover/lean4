/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering init.coe

/- Reflect a C++ name object. The VM replaces it with the C++ implementation. -/
inductive name
| anonymous  : name
| mk_string  : string → name → name
| mk_numeral : unsigned → name → name

instance : inhabited name :=
⟨name.anonymous⟩

def mk_str_name (n : name) (s : string) : name :=
name.mk_string s n

def mk_num_name (n : name) (v : nat) : name :=
name.mk_numeral (unsigned.of_nat v) n

def mk_simple_name (s : string) : name :=
mk_str_name name.anonymous s

instance string_to_name : has_coe string name :=
⟨mk_simple_name⟩

infix ` <.> `:65 := mk_str_name

open name

def name.get_prefix : name → name
| anonymous        := anonymous
| (mk_string s p)  := p
| (mk_numeral s p) := p

definition name.to_string_with_sep (sep : string) : name → string
| anonymous                := "[anonymous]"
| (mk_string s anonymous)  := s
| (mk_numeral v anonymous) := to_string v
| (mk_string s n)          := name.to_string_with_sep n ++ sep ++ s
| (mk_numeral v n)         := name.to_string_with_sep n ++ sep ++ to_string v

private def name.components' : name -> list name
| anonymous                := []
| (mk_string s n)          := mk_string s anonymous :: name.components' n
| (mk_numeral v n)         := mk_numeral v anonymous :: name.components' n

def name.components (n : name) : list name :=
  list.reverse (name.components' n)

definition name.to_string : name → string :=
  name.to_string_with_sep "."

instance : has_to_string name :=
⟨name.to_string⟩

/- TODO(Leo): provide a definition in Lean. -/
meta constant name.has_decidable_eq : decidable_eq name
/- Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order. -/
meta constant name.cmp : name → name → ordering
meta constant name.lex_cmp : name → name → ordering
meta constant name.append : name → name → name

attribute [instance] name.has_decidable_eq

meta instance : has_ordering name :=
⟨name.cmp⟩

meta instance : has_append name :=
⟨name.append⟩

/- (name.append_after n i) return a name of the form n_i -/
meta constant name.append_after : name → nat → name

meta def name.is_prefix_of : name → name → bool
| p name.anonymous := ff
| p n              :=
  if p = n then tt else name.is_prefix_of p n^.get_prefix

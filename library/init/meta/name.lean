/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.ordering init.coe

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

def name.to_string : name → string
| anonymous                := "[anonymous]"
| (mk_string s anonymous)  := s
| (mk_numeral v anonymous) := to_string v
| (mk_string s n)          := name.to_string n ++ "." ++ s
| (mk_numeral v n)         := name.to_string n ++ "." ++ to_string v

instance : has_to_string name :=
⟨name.to_string⟩

/- TODO(Leo): provide a definition in Lean. -/
meta constant name.has_decidable_eq : decidable_eq name
/- Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order. -/
meta constant name.cmp : name → name → ordering
meta constant name.lex_cmp : name → name → ordering

attribute [instance] name.has_decidable_eq

meta instance : has_ordering name :=
⟨name.cmp⟩

/- (name.append_after n i) return a name of the form n_i -/
meta constant name.append_after : name → nat → name

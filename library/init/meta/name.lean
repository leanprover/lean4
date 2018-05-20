/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering.basic init.coe init.data.to_string init.lean.name

/-- Reflect a C++ name object. The VM replaces it with the C++ implementation. -/
inductive name
| anonymous  : name
| mk_string  : name → string → name
| mk_numeral : name → uint32 → name

/-- Gadget for automatic parameter support. This is similar to the opt_param gadget, but it uses
    the tactic declaration names tac_name to synthesize the argument.
    Like opt_param, this gadget only affects elaboration.
    For example, the tactic will *not* be invoked during type class resolution. -/
@[reducible] def {u} auto_param (α : Sort u) (tac_name : name) : Sort u :=
α

@[simp] lemma {u} auto_param_eq (α : Sort u) (n : name) : auto_param α n = α :=
rfl

instance : inhabited name :=
⟨name.anonymous⟩

def mk_str_name (n : name) (s : string) : name :=
name.mk_string n s

def mk_num_name (n : name) (v : nat) : name :=
name.mk_numeral n (uint32.of_nat v)

def mk_simple_name (s : string) : name :=
mk_str_name name.anonymous s

instance string_to_name : has_coe string name :=
⟨mk_simple_name⟩

infix ` <.> `:65 := mk_str_name

open name

def name.get_prefix : name → name
| anonymous        := anonymous
| (mk_string p _)  := p
| (mk_numeral p _) := p

def name.update_prefix : name → name → name
| anonymous        new_p := anonymous
| (mk_string p s)  new_p := mk_string new_p s
| (mk_numeral p v) new_p := mk_numeral new_p v

/- The (decidable_eq string) has not been defined yet.
   So, we disable the use of if-then-else when compiling the following definitions. -/
set_option eqn_compiler.ite false

def name.to_string_with_sep (sep : string) : name → string
| anonymous                := "[anonymous]"
| (mk_string anonymous s)  := s
| (mk_numeral anonymous v) := repr v
| (mk_string n s)          := name.to_string_with_sep n ++ sep ++ s
| (mk_numeral n v)         := name.to_string_with_sep n ++ sep ++ repr v

private def name.components' : name -> list name
| anonymous                := []
| (mk_string n s)          := mk_string anonymous s :: name.components' n
| (mk_numeral n v)         := mk_numeral anonymous v :: name.components' n

def name.components (n : name) : list name :=
(name.components' n).reverse

protected def name.to_string : name → string :=
name.to_string_with_sep "."

instance : has_to_string name :=
⟨name.to_string⟩

/- TODO(Leo): provide a definition in Lean. -/
meta constant name.has_decidable_eq : decidable_eq name
/- Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order. -/
meta constant name.cmp : name → name → ordering
meta constant name.lex_cmp : name → name → ordering
meta constant name.append : name → name → name
meta constant name.is_internal : name → bool

protected meta def name.lt (a b : name) : Prop :=
name.cmp a b = ordering.lt

meta instance : decidable_rel name.lt :=
λ a b, ordering.decidable_eq _ _

meta instance : has_lt name :=
⟨name.lt⟩

attribute [instance] name.has_decidable_eq

meta instance : has_append name :=
⟨name.append⟩

/-- `name.append_after n i` return a name of the form n_i -/
meta constant name.append_after : name → nat → name

meta def name.is_prefix_of : name → name → bool
| p name.anonymous := ff
| p n              :=
  if p = n then tt else name.is_prefix_of p n.get_prefix

meta def name.replace_prefix : name → name → name → name
| anonymous        p p' := anonymous
| (mk_string c s)  p p' := if c = p then mk_string p' s else mk_string (name.replace_prefix c p p') s
| (mk_numeral c v) p p' := if c = p then mk_numeral p' v else mk_numeral (name.replace_prefix c p p') v

meta def name.to_lean_name : name → lean.name
| name.anonymous := lean.name.anonymous
| (name.mk_string n s) := n.to_lean_name.mk_string s
| (name.mk_numeral n u) := n.to_lean_name.mk_numeral u.to_nat

meta instance : has_coe name lean.name :=
⟨name.to_lean_name⟩

/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering.basic init.coe init.data.to_string init.lean.name

export lean (name name.anonymous name.mk_string name.mk_numeral mk_str_name mk_num_name mk_simple_name)

/-- Gadget for automatic parameter support. This is similar to the opt_param gadget, but it uses
    the tactic declaration names tac_name to synthesize the argument.
    Like opt_param, this gadget only affects elaboration.
    For example, the tactic will *not* be invoked during type class resolution. -/
@[reducible] def {u} auto_param (α : Sort u) (tac_name : name) : Sort u :=
α

lemma {u} auto_param_eq (α : Sort u) (n : name) : auto_param α n = α :=
rfl

infix ` <.> `:65 := mk_str_name

/- Both cmp and lex_cmp are total orders, but lex_cmp implements a lexicographical order. -/
meta constant name.cmp : name → name → ordering
meta constant name.lex_cmp : name → name → ordering
meta constant name.append : name → name → name
meta constant lean.name.is_internal : name → bool

protected meta def name.lt (a b : name) : Prop :=
name.cmp a b = ordering.lt

meta instance : decidable_rel name.lt :=
λ a b, dec_eq (name.cmp a b) ordering.lt

meta instance : has_lt name :=
⟨name.lt⟩

meta instance : has_append name :=
⟨name.append⟩

/-- `name.append_after n i` return a name of the form n_i -/
meta constant lean.name.append_after : name → nat → name

meta def lean.name.is_prefix_of : name → name → bool
| p name.anonymous := ff
| p n              :=
  if p = n then tt else lean.name.is_prefix_of p n.get_prefix

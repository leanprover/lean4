/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.level

inductive binder_info :=
| default | implicit | strict_implicit | inst_implicit | other

meta_constant macro_def : Type₁

/- Reflect a C++ expr object. The VM replaces it with the C++ implementation. -/
inductive expr :=
| var      : unsigned → expr
| sort     : level → expr
| const    : name → list level → expr
| meta     : name → expr → expr
| free_var : name → name → binder_info → expr → expr
| app      : expr → expr → expr
| lam      : name → binder_info → expr → expr → expr
| pi       : name → binder_info → expr → expr → expr
| elet     : name → expr → expr → expr → expr
| macro    : macro_def → ∀ n : unsigned, (fin (unsigned.to_nat n) → expr) → expr

meta_constant expr.mk_macro (d : macro_def) : list expr → expr
meta_definition expr.mk_var (n : nat) : expr :=
expr.var (unsigned.of_nat n)

meta_constant expr.has_decidable_eq : decidable_eq expr
attribute [instance] expr.has_decidable_eq
meta_constant expr.alpha_eqv : expr → expr → bool
notation a ` =ₐ `:50 b:50 := expr.alpha_eqv a b = bool.tt

meta_constant expr.to_string : expr → string
meta_definition expr.has_to_string [instance] : has_to_string expr :=
has_to_string.mk expr.to_string

meta_constant expr.lt : expr → expr → bool
meta_constant expr.lex_lt : expr → expr → bool
meta_definition expr.cmp (a b : expr) : cmp_result :=
if expr.lt a b = bool.tt then cmp_result.lt
else if a = b then cmp_result.eq
else cmp_result.gt

meta_constant expr.fold {A :Type} : expr → A → (expr → unsigned → A → A) → A

meta_constant expr.abstract_fv  : expr → name → expr
meta_constant expr.abstract_fvs : expr → list name → expr

meta_constant expr.instantiate_var  : expr → expr → expr
meta_constant expr.instantiate_vars : expr → list expr → expr

meta_constant expr.has_var : expr → bool
meta_constant expr.has_var_idx : expr → nat → bool
meta_constant expr.has_free_var : expr → bool
meta_constant expr.has_meta_var : expr → bool
meta_constant expr.lift_vars  : expr → nat → nat → expr
meta_constant expr.lower_vars : expr → nat → nat → expr

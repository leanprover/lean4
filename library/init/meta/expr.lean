/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.level

inductive binder_info
| default | implicit | strict_implicit | inst_implicit | other

meta constant macro_def : Type

/- Reflect a C++ expr object. The VM replaces it with the C++ implementation. -/
meta inductive expr
| var         : unsigned → expr
| sort        : level → expr
| const       : name → list level → expr
| mvar        : name → expr → expr
| local_const : name → name → binder_info → expr → expr
| app         : expr → expr → expr
| lam         : name → binder_info → expr → expr → expr
| pi          : name → binder_info → expr → expr → expr
| elet        : name → expr → expr → expr → expr
| macro       : macro_def → ∀ n : unsigned, (fin (unsigned.to_nat n) → expr) → expr

meta instance : inhabited expr :=
⟨expr.sort level.zero⟩

meta constant expr.mk_macro (d : macro_def) : list expr → expr
meta constant expr.macro_def_name (d : macro_def) : name
meta def expr.mk_var (n : nat) : expr :=
expr.var (unsigned.of_nat n)

-- Compares expressions, including binder names.
meta constant expr.has_decidable_eq : decidable_eq expr
attribute [instance] expr.has_decidable_eq

-- Compares expressions while ignoring binder names.
meta constant expr.alpha_eqv : expr → expr → bool
notation a ` =ₐ `:50 b:50 := expr.alpha_eqv a b = bool.tt

meta constant expr.to_string : expr → string

meta instance : has_to_string expr :=
has_to_string.mk expr.to_string

/- Coercion for letting users write (f a) instead of (expr.app f a) -/
meta instance : has_coe_to_fun expr :=
{ F := λ e, expr → expr, coe := λ e, expr.app e }

meta constant expr.hash : expr → nat

-- Compares expressions, ignoring binder names, and sorting by hash.
meta constant expr.lt : expr → expr → bool
-- Compares expressions, ignoring binder names.
meta constant expr.lex_lt : expr → expr → bool
-- Compares expressions, ignoring binder names, and sorting by hash.
meta def expr.cmp (a b : expr) : ordering :=
if expr.lt a b then ordering.lt
else if a =ₐ b then ordering.eq
else ordering.gt

meta constant expr.fold {α : Type} : expr → α → (expr → nat → α → α) → α
meta constant expr.replace : expr → (expr → nat → option expr) → expr

meta constant expr.abstract_local  : expr → name → expr
meta constant expr.abstract_locals : expr → list name → expr

meta def expr.abstract : expr → expr → expr
| e (expr.local_const n m bi t) := e^.abstract_local n
| e _                           := e

meta constant expr.instantiate_var  : expr → expr → expr
meta constant expr.instantiate_vars : expr → list expr → expr

meta constant expr.has_var       : expr → bool
meta constant expr.has_var_idx   : expr → nat → bool
meta constant expr.has_local     : expr → bool
meta constant expr.has_meta_var  : expr → bool
meta constant expr.lift_vars     : expr → nat → nat → expr
meta constant expr.lower_vars    : expr → nat → nat → expr
/- (copy_pos_info src tgt) copy position information from src to tgt. -/
meta constant expr.copy_pos_info : expr → expr → expr

meta constant expr.is_internal_cnstr : expr → option unsigned
meta constant expr.get_nat_value : expr → option nat

namespace expr
open decidable

-- Compares expressions, ignoring binder names, and sorting by hash.
meta instance : has_ordering expr :=
⟨ expr.cmp ⟩

meta def app_of_list : expr → list expr → expr
| f []      := f
| f (p::ps) := app_of_list (f p) ps

meta def is_app : expr → bool
| (app f a) := tt
| e         := ff

meta def app_fn : expr → expr
| (app f a) := f
| a         := a

meta def app_arg : expr → expr
| (app f a) := a
| a         := a

meta def get_app_fn : expr → expr
| (app f a) := get_app_fn f
| a         := a

meta def get_app_num_args : expr → nat
| (app f a) := get_app_num_args f + 1
| e         := 0

meta def get_app_args_aux : list expr → expr → list expr
| r (app f a) := get_app_args_aux (a::r) f
| r e         := r

meta def get_app_args : expr → list expr :=
get_app_args_aux []

meta def const_name : expr → name
| (const n ls) := n
| e            := name.anonymous

meta def is_constant : expr → bool
| (const n ls) := tt
| e            := ff

meta def is_local_constant : expr → bool
| (local_const n m bi t) := tt
| e                      := ff

meta def local_uniq_name : expr → name
| (local_const n m bi t) := n
| e                      := name.anonymous

meta def local_pp_name : expr → name
| (local_const x n bi t) := n
| e                      := name.anonymous

meta def is_constant_of : expr → name → bool
| (const n₁ ls) n₂ := to_bool (n₁ = n₂)
| e             n  := ff

meta def is_app_of (e : expr) (n : name) : bool :=
is_app e && is_constant_of (get_app_fn e) n

meta def is_napp_of (e : expr) (c : name) (n : nat) : bool :=
to_bool (is_app_of e c ∧ get_app_num_args e = n)

meta def is_false (e : expr) : bool :=
is_constant_of e `false

meta def is_not : expr → option expr
| (app f a)     := if is_constant_of f `not then some a else none
| (pi n bi a b) := if is_false b then some a else none
| e             := none

meta def is_eq (e : expr) : option (expr × expr) :=
if is_napp_of e `eq 3
then some (app_arg (app_fn e), app_arg e)
else none

meta def is_ne (e : expr) : option (expr × expr) :=
if is_napp_of e `ne 3
then some (app_arg (app_fn e), app_arg e)
else none

meta def is_bin_arith_app (e : expr) (op : name) : option (expr × expr) :=
if is_napp_of e op 4
then some (app_arg (app_fn e), app_arg e)
else none

meta def is_lt (e : expr) : option (expr × expr) :=
is_bin_arith_app e `lt

meta def is_gt (e : expr) : option (expr × expr) :=
is_bin_arith_app e `gt

meta def is_le (e : expr) : option (expr × expr) :=
is_bin_arith_app e `le

meta def is_ge (e : expr) : option (expr × expr) :=
is_bin_arith_app e `ge

meta def is_heq (e : expr) : option (expr × expr × expr × expr) :=
if is_napp_of e `heq 4
then some (app_arg (app_fn (app_fn (app_fn e))),
           app_arg (app_fn (app_fn e)),
           app_arg (app_fn e),
           app_arg e)
else none

meta def is_pi : expr → bool
| (pi n bi d b) := tt
| e             := ff

meta def is_arrow : expr → bool
| (pi n bi d b) := bnot (has_var b)
| e             := ff

meta def is_let : expr → bool
| (elet n t v b) := tt
| e              := ff

meta def binding_name : expr → name
| (pi n m d b)  := n
| (lam n m d b) := n
| e             := name.anonymous

meta def binding_info : expr → binder_info
| (pi n bi d b)  := bi
| (lam n bi d b) := bi
| e              := binder_info.default

meta def binding_domain : expr → expr
| (pi n bi d b)  := d
| (lam n bi d b) := d
| e             := e

meta def binding_body : expr → expr
| (pi n bi d b)  := b
| (lam n bi d b) := b
| e             := e

meta def prop : expr := expr.sort level.zero

end expr

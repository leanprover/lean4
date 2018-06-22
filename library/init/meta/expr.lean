/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.level init.control.monad init.lean.expr init.meta.format
universes u v

-- TODO(Leo): move this stuff to a different place
structure pos :=
(line   : nat)
(column : nat)

instance : decidable_eq pos
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := if h₁ : l₁ = l₂ then
  if h₂ : c₁ = c₂ then is_true (eq.rec_on h₁ (eq.rec_on h₂ rfl))
  else is_false (λ contra, pos.no_confusion contra (λ e₁ e₂, absurd e₂ h₂))
else is_false (λ contra, pos.no_confusion contra (λ e₁ e₂, absurd e₁ h₁))

meta instance : has_to_format pos :=
⟨λ ⟨l, c⟩, "⟨" ++ l ++ ", " ++ c ++ "⟩"⟩

export lean (expr binder_info kvmap expr.bvar expr.fvar expr.sort expr.const expr.mvar expr.app expr.lam expr.pi expr.elet expr.lit expr.mdata expr.proj expr.quote)

def expr.mk_bvar (n : nat) : expr :=
expr.bvar n

/-- Compares expressions, including binder names. -/
meta constant lean.expr.has_decidable_eq : decidable_eq expr
attribute [instance] lean.expr.has_decidable_eq

/-- Compares expressions while ignoring binder names. -/
meta constant lean.expr.alpha_eqv : expr → expr → bool
notation a ` =ₐ `:50 b:50 := lean.expr.alpha_eqv a b = bool.tt

protected meta constant lean.expr.to_string : expr → string

meta instance : has_to_string (expr) := ⟨lean.expr.to_string⟩
meta instance : has_to_format (expr) := ⟨λ e, e.to_string⟩

/- Coercion for letting users write (f a) instead of (expr.app f a) -/
meta instance : has_coe_to_fun (expr) :=
{ F := λ e, expr → expr, coe := λ e, expr.app e }

meta constant lean.expr.hash : expr → nat

/-- Compares expressions, ignoring binder names, and sorting by hash. -/
meta constant lean.expr.lt : expr → expr → bool
/-- Compares expressions, ignoring binder names. -/
meta constant lean.expr.lex_lt : expr → expr → bool

meta constant lean.expr.fold {α : Type} : expr → α → (expr → nat → α → α) → α

/-- `has_var e` returns true iff e has free variables. -/
meta constant lean.expr.has_bvar_idx   : expr → nat → bool

/-- (reflected a) is a special opaque container for a closed `expr` representing `a`.
    It can only be obtained via type class inference, which will use the representation
    of `a` in the calling context. Local constants in the representation are replaced
    by nested inference of `reflected` instances.

    The quotation expression `(a) (outside of patterns) is equivalent to `reflect a`
    and thus can be used as an explicit way of inferring an instance of `reflected a`. -/
@[class] meta def reflected {α : Sort u} : α → Type :=
λ _, expr

@[inline] meta def reflected.to_expr {α : Sort u} {a : α} : reflected a → expr :=
id

@[instance] protected meta constant lean.expr.reflect (e : expr) : reflected e
@[instance] protected meta constant string.reflect (s : string) : reflected s

protected meta constant lean.expr.subst : expr → expr → expr

@[inline] meta def reflected.subst {α : Sort v} {β : α → Sort u} {f : Π a : α, β a} {a : α} :
  reflected f → reflected a → reflected (f a) :=
λ ef ea, match ef with
| (expr.lam _ _ _ _) := (lean.expr.subst ef ea)
| _                  := expr.app ef ea

attribute [irreducible] reflected reflected.subst reflected.to_expr

@[inline] meta instance {α : Sort u} (a : α) : has_coe (reflected a) expr :=
⟨reflected.to_expr⟩

protected meta def reflect {α : Sort u} (a : α) [h : reflected a] : reflected a := h

meta instance {α} (a : α) : has_to_format (reflected a) :=
⟨λ h, to_fmt h.to_expr⟩

namespace lean.expr
open decidable

def app_fn : expr → expr
| (app f a) := f
| a         := a

def app_arg : expr → expr
| (app f a) := a
| a         := a

def get_app_fn : expr → expr
| (app f a) := get_app_fn f
| a         := a

def get_app_num_args : expr → nat
| (app f a) := get_app_num_args f + 1
| e         := 0

def get_app_args_aux : list expr → expr → list expr
| r (app f a) := get_app_args_aux (a::r) f
| r e         := r

def get_app_args : expr → list expr :=
get_app_args_aux []

def mk_app : expr → list expr → expr
| e []      := e
| e (x::xs) := mk_app (lean.expr.app e x) xs

def const_name : expr → name
| (const n ls) := n
| e            := name.anonymous

def is_constant : expr → bool
| (const n ls) := tt
| e            := ff

def is_fvar : expr → bool
| (fvar n) := tt
| e        := ff

def fvar_id : expr → name
| (fvar n) := n
| e        := name.anonymous

def is_constant_of : expr → name → bool
| (const n₁ ls) n₂ := n₁ = n₂
| e             n  := ff

def is_app_of (e : expr) (n : name) : bool :=
is_constant_of (get_app_fn e) n

def is_napp_of (e : expr) (c : name) (n : nat) : bool :=
is_app_of e c ∧ get_app_num_args e = n

def is_eq : expr → option (expr × expr)
| `((%%a : %%_) = %%b) := some (a, b)
| _                    := none

def is_pi : expr → bool
| (pi _ _ _ _) := tt
| e            := ff

def is_let : expr → bool
| (elet _ _ _ _) := tt
| e              := ff

open format

end lean.expr

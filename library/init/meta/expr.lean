/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.level init.category.monad init.meta.rb_map
universes u v
open native
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

inductive binder_info
| default | implicit | strict_implicit | inst_implicit | aux_decl

instance : has_repr binder_info :=
⟨λ bi, match bi with
| binder_info.default := "default"
| binder_info.implicit := "implicit"
| binder_info.strict_implicit := "strict_implicit"
| binder_info.inst_implicit := "inst_implicit"
| binder_info.aux_decl := "aux_decl"
end⟩

meta constant macro_def : Type

/-- Reflect a C++ expr object. The VM replaces it with the C++ implementation. -/
meta inductive expr (elaborated : bool := tt)
| var      {} : nat → expr
| sort     {} : level → expr
| const    {} : name → list level → expr
| mvar        : name → name → expr → expr
| local_const : name → name → binder_info → expr → expr
| app         : expr → expr → expr
| lam         : name → binder_info → expr → expr → expr
| pi          : name → binder_info → expr → expr → expr
| elet        : name → expr → expr → expr → expr
| macro       : macro_def → list expr → expr

variable {elab : bool}

meta instance : inhabited expr :=
⟨expr.sort level.zero⟩

meta constant expr.macro_def_name (d : macro_def) : name
meta def expr.mk_var (n : nat) : expr :=
expr.var n

/- Expressions can be annotated using the annotation macro. -/
meta constant expr.is_annotation : expr elab → option (name × expr elab)

meta def expr.erase_annotations : expr elab → expr elab
| e :=
  match e.is_annotation with
  | some (_, a) := expr.erase_annotations a
  | none        := e
  end

/-- Compares expressions, including binder names. -/
meta constant expr.has_decidable_eq : decidable_eq expr
attribute [instance] expr.has_decidable_eq

/-- Compares expressions while ignoring binder names. -/
meta constant expr.alpha_eqv : expr → expr → bool
notation a ` =ₐ `:50 b:50 := expr.alpha_eqv a b = bool.tt

protected meta constant expr.to_string : expr elab → string

meta instance : has_to_string (expr elab) := ⟨expr.to_string⟩
meta instance : has_to_format (expr elab) := ⟨λ e, e.to_string⟩

/- Coercion for letting users write (f a) instead of (expr.app f a) -/
meta instance : has_coe_to_fun (expr elab) :=
{ F := λ e, expr elab → expr elab, coe := λ e, expr.app e }

meta constant expr.hash : expr → nat

/-- Compares expressions, ignoring binder names, and sorting by hash. -/
meta constant expr.lt : expr → expr → bool
/-- Compares expressions, ignoring binder names. -/
meta constant expr.lex_lt : expr → expr → bool

meta constant expr.fold {α : Type} : expr → α → (expr → nat → α → α) → α
meta constant expr.replace : expr → (expr → nat → option expr) → expr

meta constant expr.abstract_local  : expr → name → expr
meta constant expr.abstract_locals : expr → list name → expr

meta def expr.abstract : expr → expr → expr
| e (expr.local_const n m bi t) := e.abstract_local n
| e _                           := e

meta constant expr.instantiate_univ_params : expr → list (name × level) → expr
meta constant expr.instantiate_var         : expr → expr → expr
meta constant expr.instantiate_vars        : expr → list expr → expr

protected meta constant expr.subst : expr elab → expr elab → expr elab

/-- `has_var e` returns true iff e has free variables. -/
meta constant expr.has_var       : expr → bool
meta constant expr.has_var_idx   : expr → nat → bool
meta constant expr.has_local     : expr → bool
meta constant expr.has_meta_var  : expr → bool
/-- `lower_vars e s d` lowers the free variables >= s in `e` by `d`. That is, a free variable `var i` s.t.
   `i >= s` is mapped to `var (i-d)`. -/
meta constant expr.lower_vars    : expr → nat → nat → expr
/-- Lifts free variables. See `expr.lower_vars` for details. -/
meta constant expr.lift_vars     : expr → nat → nat → expr
protected meta constant expr.pos : expr elab → option pos
/-- `copy_pos_info src tgt` copies position information from `src` to `tgt`. -/
meta constant expr.copy_pos_info : expr → expr → expr

meta constant expr.is_internal_cnstr : expr → option unsigned
meta constant expr.get_nat_value : expr → option nat

meta constant expr.collect_univ_params : expr → list name
/-- `occurs e t` returns `tt` iff `e` occurs in `t` -/
meta constant expr.occurs        : expr → expr → bool

meta constant expr.has_local_in : expr → name_set → bool

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

@[inline] meta def reflected.subst {α : Sort v} {β : α → Sort u} {f : Π a : α, β a} {a : α} :
  reflected f → reflected a → reflected (f a) :=
λ ef ea, match ef with
| (expr.lam _ _ _ _) := expr.subst ef ea
| _                  := expr.app   ef ea
end

attribute [irreducible] reflected reflected.subst reflected.to_expr

@[instance] protected meta constant expr.reflect (e : expr elab) : reflected e
@[instance] protected meta constant string.reflect (s : string) : reflected s

@[inline] meta instance {α : Sort u} (a : α) : has_coe (reflected a) expr :=
⟨reflected.to_expr⟩

protected meta def reflect {α : Sort u} (a : α) [h : reflected a] : reflected a := h

meta instance {α} (a : α) : has_to_format (reflected a) :=
⟨λ h, to_fmt h.to_expr⟩

namespace expr
open decidable

meta def expr.lt_prop (a b : expr) : Prop :=
expr.lt a b = tt

meta instance : decidable_rel expr.lt_prop :=
λ a b, bool.decidable_eq _ _

/-- Compares expressions, ignoring binder names, and sorting by hash. -/
meta instance : has_lt expr :=
⟨ expr.lt_prop ⟩

meta def mk_true : expr :=
const `true []

meta def mk_false : expr :=
const `false []

/-- Returns the sorry macro with the given type. -/
meta constant mk_sorry (type : expr) : expr
/-- Checks whether e is sorry, and returns its type. -/
meta constant is_sorry (e : expr) : option expr

meta def instantiate_local (n : name) (s : expr) (e : expr) : expr :=
instantiate_var (abstract_local e n) s

meta def instantiate_locals (s : list (name × expr)) (e : expr) : expr :=
instantiate_vars (abstract_locals e (list.reverse (list.map prod.fst s))) (list.map prod.snd s)

meta def is_var : expr → bool
| (var _) := tt
| _       := ff

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

meta def get_app_fn : expr elab → expr elab
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

meta def mk_app : expr → list expr → expr
| e []      := e
| e (x::xs) := mk_app (e x) xs

meta def mk_binding (ctor : name → binder_info → expr → expr → expr) (e : expr) : Π (l : expr), expr
| (local_const n pp_n bi ty) := ctor pp_n bi ty (e.abstract_local n)
| _                          := e

/-- (bind_pi e l) abstracts and pi-binds the local `l` in `e` -/
meta def bind_pi := mk_binding pi
/-- (bind_lambda e l) abstracts and lambda-binds the local `l` in `e` -/
meta def bind_lambda := mk_binding lam

meta def ith_arg_aux : expr → nat → expr
| (app f a) 0     := a
| (app f a) (n+1) := ith_arg_aux f n
| e         _     := e

meta def ith_arg (e : expr) (i : nat) : expr :=
ith_arg_aux e (get_app_num_args e - i - 1)

meta def const_name : expr elab → name
| (const n ls) := n
| e            := name.anonymous

meta def is_constant : expr elab → bool
| (const n ls) := tt
| e            := ff

meta def is_local_constant : expr → bool
| (local_const n m bi t) := tt
| e                      := ff

meta def local_uniq_name : expr → name
| (local_const n m bi t) := n
| e                      := name.anonymous

meta def local_pp_name : expr elab → name
| (local_const x n bi t) := n
| e                      := name.anonymous

meta def local_type : expr elab → expr elab
| (local_const _ _ _ t) := t
| e := e

meta def is_aux_decl : expr → bool
| (local_const _ _ binder_info.aux_decl _) := tt
| _                                        := ff

meta def is_constant_of : expr elab → name → bool
| (const n₁ ls) n₂ := n₁ = n₂
| e             n  := ff

meta def is_app_of (e : expr) (n : name) : bool :=
is_constant_of (get_app_fn e) n

meta def is_napp_of (e : expr) (c : name) (n : nat) : bool :=
is_app_of e c ∧ get_app_num_args e = n

meta def is_false : expr → bool
| `(false) := tt
| _         := ff

meta def is_not : expr → option expr
| `(not %%a)     := some a
| `(%%a → false) := some a
| e              := none

meta def is_and : expr → option (expr × expr)
| `(and %%α %%β) := some (α, β)
| _              := none

meta def is_or : expr → option (expr × expr)
| `(or %%α %%β) := some (α, β)
| _             := none

meta def is_iff : expr → option (expr × expr)
| `((%%a : Prop) ↔ %%b) := some (a, b)
| _                     := none

meta def is_eq : expr → option (expr × expr)
| `((%%a : %%_) = %%b) := some (a, b)
| _                    := none

meta def is_ne : expr → option (expr × expr)
| `((%%a : %%_) ≠ %%b) := some (a, b)
| _                    := none

meta def is_bin_arith_app (e : expr) (op : name) : option (expr × expr) :=
if is_napp_of e op 4
then some (app_arg (app_fn e), app_arg e)
else none

meta def is_lt (e : expr) : option (expr × expr) :=
is_bin_arith_app e ``has_lt.lt

meta def is_gt (e : expr) : option (expr × expr) :=
is_bin_arith_app e ``gt

meta def is_le (e : expr) : option (expr × expr) :=
is_bin_arith_app e ``has_le.le

meta def is_ge (e : expr) : option (expr × expr) :=
is_bin_arith_app e ``ge

meta def is_heq : expr → option (expr × expr × expr × expr)
| `(@heq %%α %%a %%β %%b) := some (α, a, β, b)
| _                       := none

meta def is_lambda : expr → bool
| (lam _ _ _ _) := tt
| e             := ff

meta def is_pi : expr → bool
| (pi _ _ _ _) := tt
| e            := ff

meta def is_arrow : expr → bool
| (pi _ _ _ b) := bnot (has_var b)
| e            := ff

meta def is_let : expr → bool
| (elet _ _ _ _) := tt
| e              := ff

meta def binding_name : expr → name
| (pi n _ _ _)  := n
| (lam n _ _ _) := n
| e             := name.anonymous

meta def binding_info : expr → binder_info
| (pi _ bi _ _)  := bi
| (lam _ bi _ _) := bi
| e              := binder_info.default

meta def binding_domain : expr → expr
| (pi _ _ d _)  := d
| (lam _ _ d _) := d
| e             := e

meta def binding_body : expr → expr
| (pi _ _ _ b)  := b
| (lam _ _ _ b) := b
| e             := e

meta def is_macro : expr → bool
| (macro d a) := tt
| e           := ff

meta def is_numeral : expr → bool
| `(@has_zero.zero %%α %%s)  := tt
| `(@has_one.one %%α %%s)    := tt
| `(@bit0 %%α %%s %%v)       := is_numeral v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := is_numeral v
| _                          := ff

meta def imp (a b : expr) : expr :=
pi `_ binder_info.default a b

meta def lambdas : list expr → expr → expr
| (local_const uniq pp info t :: es) f :=
  lam pp info t (abstract_local (lambdas es f) uniq)
| _ f := f

meta def pis : list expr → expr → expr
| (local_const uniq pp info t :: es) f :=
  pi pp info t (abstract_local (pis es f) uniq)
| _ f := f

meta def extract_opt_auto_param : expr → expr
| `(@opt_param %%t _)  := extract_opt_auto_param t
| `(@auto_param %%t _) := extract_opt_auto_param t
| e                    := e

open format

private meta def p := λ xs, paren (format.join (list.intersperse " " xs))

meta def to_raw_fmt : expr elab → format
| (var n) := p ["var", to_fmt n]
| (sort l) := p ["sort", to_fmt l]
| (const n ls) := p ["const", to_fmt n, to_fmt ls]
| (mvar n m t)   := p ["mvar", to_fmt n, to_fmt m, to_raw_fmt t]
| (local_const n m bi t) := p ["local_const", to_fmt n, to_fmt m, to_raw_fmt t]
| (app e f) := p ["app", to_raw_fmt e, to_raw_fmt f]
| (lam n bi e t) := p ["lam", to_fmt n, repr bi, to_raw_fmt e, to_raw_fmt t]
| (pi n bi e t) := p ["pi", to_fmt n, repr bi, to_raw_fmt e, to_raw_fmt t]
| (elet n g e f) := p ["elet", to_fmt n, to_raw_fmt g, to_raw_fmt e, to_raw_fmt f]
| (macro d args) := sbracket (format.join (list.intersperse " " ("macro" :: to_fmt (macro_def_name d) :: args.map to_raw_fmt)))

meta def mfold {α : Type} {m : Type → Type} [monad m] (e : expr) (a : α) (fn : expr → nat → α → m α) : m α :=
fold e (return a) (λ e n a, a >>= fn e n)

end expr

@[reducible] meta def expr_map (data : Type) := rb_map expr data
namespace expr_map
export native.rb_map (hiding mk)

meta def mk (data : Type) : expr_map data := rb_map.mk expr data
end expr_map

meta def mk_expr_map {data : Type} : expr_map data :=
expr_map.mk data

@[reducible] meta def expr_set := rb_set expr
meta def mk_expr_set : expr_set := mk_rb_set

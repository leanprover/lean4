/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.rewrite_tactic init.meta.simp_tactic
import init.meta.defeq_simp_tactic

namespace tactic
namespace interactive
namespace types
/- The parser treats constants in the tactic.interactice namespace specially.
   The following argument types have special parser support when interactive tactics
   are used inside `begin ... end` blocks.

   - ident : make sure the next token is an identifier, and
             produce the quoted name `t, where t is the next identifier.

   - opt_ident : parse (identifier)?

   - using_ident

   - raw_ident_list : parse identifier* and produce a list of quoted identifiers.

         Example:
           a b c
         produces
           [`a, `b, `c]

   - with_ident_list : parse
                 (`with` identifier+)?
                 and produce a list of quoted identifiers

   - assign_tk : parse the token `:=` and produce the unit ()
   - colon_tk : parse the token `:` and produce the unit ()
   - comma_tk : parse the token `,` and produce the unit ()

   - location : parse
             (`at` identifier+)?
             and produce a list of quoted identifiers

   - qexpr : parse an expression e and produce the quoted expression `e

   - qexpr_list : parse
           `[` (expr (`,` expr)*)? `]`

            and produce a list of quoted expressions.

   - opt_qexpr_list : parse
           (`[` (expr (`,` expr)*)? `]`)?

           and produce a list of quoted expressions.

   - qexpr0 : parse an expression e using 0 as the right-binding-power,
              and produce the quoted expression `e

   - qexpr_list_or_qexpr0 : parse
           `[` (expr (`,` expr)*)? `]`
            or
            expr

            and produce a list of quoted expressions

  - itactic: parse a nested "interactive" tactic. That is, parse
           `(` tactic `)`
-/
def ident : Type := name
def opt_ident : Type := option ident
def using_ident : Type := option ident
def raw_ident_list : Type := list ident
def with_ident_list : Type := list ident
def without_ident_list : Type := list ident
def location : Type := list ident
@[reducible] meta def qexpr : Type := pexpr
@[reducible] meta def qexpr0 : Type := pexpr
meta def qexpr_list : Type := list qexpr
meta def opt_qexpr_list : Type := list qexpr
meta def qexpr_list_or_qexpr0 : Type := list qexpr
meta def itactic : Type := tactic unit
meta def assign_tk : Type := unit
meta def colon_tk : Type := unit
end types

open types expr

meta def intro : opt_ident → tactic unit
| none     := intro1 >> skip
| (some h) := tactic.intro h >> skip

meta def intros : raw_ident_list → tactic unit
| [] := tactic.intros >> skip
| hs := intro_lst hs >> skip

meta def apply (q : qexpr0) : tactic unit :=
to_expr q >>= tactic.apply

meta def refine : qexpr0 → tactic unit :=
tactic.refine

meta def assumption : tactic unit :=
tactic.assumption

meta def change (q : qexpr0) : tactic unit :=
to_expr_strict q >>= tactic.change

meta def exact (q : qexpr0) : tactic unit :=
do tgt : expr ← target,
   to_expr_strict `((%%q : %%tgt)) >>= tactic.exact

private meta def get_locals : list name → tactic (list expr)
| []      := return []
| (n::ns) := do h ← get_local n, hs ← get_locals ns, return (h::hs)

meta def revert (ids : raw_ident_list) : tactic unit :=
do hs ← get_locals ids, revert_lst hs, skip

/- Return (some a) iff p is of the form (- a) -/
private meta def is_neg (p : pexpr) : option pexpr :=
/- Remark: we use the low-level to_raw_expr and of_raw_expr to be able to
   pattern match pre-terms. This is a low-level trick (aka hack). -/
match pexpr.to_raw_expr p with
| (app (const c []) arg) := if c = `neg then some (pexpr.of_raw_expr arg) else none
| _                      := none
end

private meta def resolve_name (n : name) : tactic expr :=
get_local n
<|>
mk_const n
<|>
fail ("failed to resolve name '" ++ to_string n ++ "'")

/- Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/
private meta def to_expr' (p : pexpr) : tactic expr :=
match pexpr.to_raw_expr p with
| (const c [])          := resolve_name c
| (local_const c _ _ _) := resolve_name c
| _                     := to_expr p
end

private meta def to_symm_expr_list : list pexpr → tactic (list (bool × expr))
| []      := return []
| (p::ps) :=
  match is_neg p with
  | some a :=  do r ← to_expr' a, rs ← to_symm_expr_list ps, return ((tt, r) :: rs)
  | none   :=  do r ← to_expr' p, rs ← to_symm_expr_list ps, return ((ff, r) :: rs)
  end

private meta def rw_goal : transparency → list (bool × expr) → tactic unit
| m []              := return ()
| m ((symm, e)::es) := rewrite_core m tt occurrences.all symm e >> rw_goal m es

private meta def rw_hyp : transparency → list (bool × expr) → name → tactic unit
| m []              hname := return ()
| m ((symm, e)::es) hname :=
  do h ← get_local hname,
     rewrite_at_core m tt occurrences.all symm e h,
     rw_hyp m es hname

private meta def rw_hyps : transparency → list (bool × expr) → list name → tactic unit
| m es  []      := return ()
| m es  (h::hs) := rw_hyp m es h >> rw_hyps m es hs

private meta def rw_core (m : transparency) (hs : qexpr_list_or_qexpr0) (loc : location) : tactic unit :=
do hlist ← to_symm_expr_list hs,
   match loc with
   | [] := rw_goal m hlist >> try reflexivity
   | hs := rw_hyps m hlist hs >> try reflexivity
   end

meta def rewrite : qexpr_list_or_qexpr0 → location → tactic unit :=
rw_core reducible

meta def rw : qexpr_list_or_qexpr0 → location → tactic unit :=
rewrite

meta def erewrite : qexpr_list_or_qexpr0 → location → tactic unit :=
rw_core semireducible

meta def erw : qexpr_list_or_qexpr0 → location → tactic unit :=
erewrite

private meta def get_type_name (e : expr) : tactic name :=
do e_type ← infer_type e >>= whnf,
   (const I ls) ← return $ get_app_fn e_type | failed,
   return I

meta def induction (p : qexpr0) (rec_name : using_ident) (ids : with_ident_list) : tactic unit :=
do e ← to_expr p,
   match rec_name with
   | some n := induction_core semireducible e n ids
   | none   := do I ← get_type_name e, induction_core semireducible e (I <.> "rec") ids
   end

meta def cases (p : qexpr0) (ids : with_ident_list) : tactic unit :=
do e ← to_expr p,
   cases_core semireducible e ids

meta def generalize (p : qexpr) (x : ident) : tactic unit :=
do e ← to_expr p,
   tactic.generalize e x

meta def trivial : tactic unit :=
tactic.triv <|> tactic.reflexivity <|> tactic.contradiction <|> fail "trivial tactic failed"

meta def contradiction : tactic unit :=
tactic.contradiction

meta def repeat : itactic → tactic unit :=
tactic.repeat

meta def assert (h : ident) (c : colon_tk) (q : qexpr0) : tactic unit :=
do e ← to_expr_strict q,
   tactic.assert h e

meta def define (h : ident) (c : colon_tk) (q : qexpr0) : tactic unit :=
do e ← to_expr_strict q,
   tactic.define h e

meta def assertv (h : ident) (c : colon_tk) (q₁ : qexpr0) (a : assign_tk) (q₂ : qexpr0) : tactic unit :=
do t ← to_expr_strict q₁,
   v ← to_expr_strict `((%%q₂ : %%t)),
   tactic.assertv h t v

meta def definev (h : ident) (c : colon_tk) (q₁ : qexpr0) (a : assign_tk) (q₂ : qexpr0) : tactic unit :=
do t ← to_expr_strict q₁,
   v ← to_expr_strict `((%%q₂ : %%t)),
   tactic.definev h t v

meta def note (h : ident) (a : assign_tk) (q : qexpr0) : tactic unit :=
do p ← to_expr_strict q,
   tactic.note h p

meta def trace_state : tactic unit :=
tactic.trace_state

meta definition trace {A : Type} [has_to_tactic_format A] (a : A) : tactic unit :=
tactic.trace a

meta definition existsi (e : qexpr0) : tactic unit :=
to_expr e >>= tactic.existsi

meta definition constructor : tactic unit :=
tactic.constructor

meta definition left : tactic unit :=
tactic.left

meta definition right : tactic unit :=
tactic.right

meta definition split : tactic unit :=
tactic.split

meta definition injection (q : qexpr0) (hs : with_ident_list) : tactic unit :=
do e ← to_expr q, tactic.injection_with e hs

private meta def to_expr_list : list pexpr → tactic (list expr)
| []      := return []
| (p::ps) := do e ← to_expr' p, es ← to_expr_list ps, return (e :: es)

private meta def mk_simp_set (hs : list qexpr) (ex : list name) : tactic simp_lemmas :=
do es ← to_expr_list hs,
   s₀ ← mk_simp_lemmas,
   s₁ ← simp_lemmas_add_extra reducible s₀ es,
   return $ simp_lemmas_erase s₁ ex

private meta def simp_goal : simp_lemmas → tactic unit
| s := do
   (new_target, Heq) ← target >>= simplify_core (simp_goal s) `eq s,
   tactic.assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_app `eq.mpr [Heq, Ht] >>= tactic.exact

private meta def simp_hyp (s : simp_lemmas) (h_name : name) : tactic unit :=
do h     ← get_local h_name,
   htype ← infer_type h,
   (new_htype, eqpr) ← simplify_core (simp_goal s) `eq s htype,
   tactic.assert (expr.local_pp_name h) new_htype,
   mk_app `eq.mp [eqpr, h] >>= tactic.exact,
   try $ tactic.clear h

private meta definition simp_hyps : simp_lemmas → location → tactic unit
| s []      := skip
| s (h::hs) := simp_hyp s h >> simp_hyps s hs

meta definition simp (hs : opt_qexpr_list) (ids : without_ident_list) (loc : location) : tactic unit :=
do s ← mk_simp_set hs ids,
   match loc : _ → tactic unit with
   | [] := simp_goal s
   | _  := simp_hyps s loc
   end,
   try tactic.triv, try tactic.reflexivity

private meta def dsimp_hyps : location → tactic unit
| []      := skip
| (h::hs) := get_local h >>= dsimp_at

meta def dsimp : location → tactic unit
| [] := tactic.dsimp
| hs := dsimp_hyps hs

meta def reflexivity : tactic unit :=
tactic.reflexivity

meta def symmetry : tactic unit :=
tactic.symmetry

meta def transitivity : tactic unit :=
tactic.transitivity

meta def subst (q : qexpr0) : tactic unit :=
to_expr q >>= tactic.subst >> try reflexivity

meta def clear : raw_ident_list → tactic unit :=
tactic.clear_lst

end interactive
end tactic

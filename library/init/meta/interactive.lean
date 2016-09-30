/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.rewrite_tactic

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

   - qexpr0 : parse an expression e using 0 as the right-binding-power,
              and produce the quoted expression `e

   - qexpr_list_or_qexpr0 : parse
           `[` (expr (`,` expr)*)? `]`
            or
            expr

            and produce a list of quoted expressions

  - itactic: parse a nested "interactive" tactic -/
def ident : Type := name
def opt_ident : Type := option ident
def using_ident : Type := option ident
def raw_ident_list : Type := list ident
def with_ident_list : Type := list ident
def location : Type := list ident
@[reducible] meta def qexpr : Type := pexpr
@[reducible] meta def qexpr0 : Type := pexpr
meta def qexpr_list : Type := list qexpr
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

private meta def rw_goal : list (bool × expr) → tactic unit
| []              := return ()
| ((symm, e)::es) := rewrite_core reducible tt occurrences.all symm e >> rw_goal es

private meta def rw_hyp : list (bool × expr) → name → tactic unit
| []              hname := return ()
| ((symm, e)::es) hname :=
  do h ← get_local hname,
     rewrite_at_core reducible tt occurrences.all symm e h,
     rw_hyp es hname

private meta def rw_hyps : list (bool × expr) → list name → tactic unit
| es  []      := return ()
| es  (h::hs) := rw_hyp es h >> rw_hyps es hs

meta def rewrite (hs : qexpr_list_or_qexpr0) (loc : location) : tactic unit :=
do hlist ← to_symm_expr_list hs,
   match loc with
   | [] := rw_goal hlist >> try reflexivity
   | hs := rw_hyps hlist hs >> try reflexivity
   end

meta def rw : qexpr_list_or_qexpr0 → location → tactic unit :=
rewrite

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

end interactive
end tactic

/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.rewrite_tactic init.meta.simp_tactic
import init.meta.smt.congruence_closure init.category.combinators

namespace interactive
namespace types
/- The parser treats constants in the tactic.interactive namespace specially.
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

   - qexpr_list_with_pos
   - qexpr_list_or_qexpr0_with_pos : parse
           `[` (expr (`,` expr)*)? `]`
            or
            expr

            and produce a list of quoted expressions with position information

-/
def pos : Type := nat × nat
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
meta def qexpr_list_with_pos : Type := list (qexpr × pos)
meta def opt_qexpr_list : Type := list qexpr
meta def qexpr_list_or_qexpr0 : Type := list qexpr
meta def qexpr_list_or_qexpr0_with_pos : Type := list (qexpr × pos)
meta def assign_tk : Type := unit
meta def colon_tk : Type := unit
end types
end interactive

namespace tactic
meta def report_resolve_name_failure {α : Type} (e : expr) (n : name) : tactic α :=
if e^.is_choice_macro
then fail ("failed to resolve name '" ++ to_string n ++ "', it is overloaded")
else fail ("failed to resolve name '" ++ to_string n ++ "', unexpected result")

/- allows metavars and report errors -/
meta def i_to_expr (q : pexpr) : tactic expr :=
to_expr q tt tt

/- doesn't allows metavars and report errors -/
meta def i_to_expr_strict (q : pexpr) : tactic expr :=
to_expr q ff tt

namespace interactive
open interactive.types expr

/-
itactic: parse a nested "interactive" tactic. That is, parse
  `(` tactic `)`
-/
meta def itactic : Type :=
tactic unit

/-
irtactic: parse a nested "interactive" tactic. That is, parse
  `(` tactic `)`
It is similar to itactic, but the interactive mode will report errors
when any of the nested tactics fail. This is good for tactics such as asynch and abstact.
-/
meta def irtactic : Type :=
tactic unit

/--
This tactic applies to a goal that is either a Pi/forall or starts with a let binder.

If the current goal is a Pi/forall `∀ x:T, U` (resp `let x:=t in U`) then intro puts `x:T` (resp `x:=t`) in the local context. The new subgoal target is `U`.

If the goal is an arrow `T → U`, then it puts in the local context either `h:T`, and the new goal target is `U`.

If the goal is neither a Pi/forall nor starting with a let definition,
the tactic `intro` applies the tactic `whnf` until the tactic `intro` can be applied or the goal is not `head-reducible`.
-/
meta def intro : opt_ident → tactic unit
| none     := intro1 >> skip
| (some h) := tactic.intro h >> skip

/--
Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.
The variant `intros h_1 ... h_n` introduces `n` new hypotheses using the given identifiers to name them.
-/
meta def intros : raw_ident_list → tactic unit
| [] := tactic.intros >> skip
| hs := intro_lst hs >> skip

/--
The tactic `rename h₁ h₂` renames hypothesis `h₁` into `h₂` in the current local context.
-/
meta def rename : ident → ident → tactic unit :=
tactic.rename

/--
This tactic applies to any goal.
The argument term is a term well-formed in the local context of the main goal.
The tactic apply tries to match the current goal against the conclusion of the type of term.
If it succeeds, then the tactic returns as many subgoals as the number of non-dependent premises
that have not been fixed by type inference or type class resolution.

The tactic `apply` uses higher-order pattern matching, type class resolution, and
first-order unification with dependent types.
-/
meta def apply (q : qexpr0) : tactic unit :=
i_to_expr q >>= tactic.apply

/--
Similar to the `apply` tactic, but it also creates subgoals for dependent premises
that have not been fixed by type inference or type class resolution.
-/
meta def fapply (q : qexpr0) : tactic unit :=
i_to_expr q >>= tactic.fapply

/--
This tactic tries to close the main goal `... |- U` using type class resolution.
It succeeds if it generates a term of type `U` using type class resolution.
-/
meta def apply_instance : tactic unit :=
tactic.apply_instance

/--
This tactic applies to any goal. It behaves like `exact` with a big difference:
the user can leave some holes `_` in the term.
`refine` will generate as many subgoals as there are holes in the term.
Note that some holes may be implicit.
The type of holes must be either synthesized by the system or declared by
an explicit type ascription like (e.g., `(_ : nat → Prop)`).
-/
meta def refine (q : qexpr0) : tactic unit :=
tactic.refine q tt

/--
This tactic looks in the local context for an hypothesis which type is equal to the goal target.
If it is the case, the subgoal is proved. Otherwise, it fails.
-/
meta def assumption : tactic unit :=
tactic.assumption

/--
This tactic applies to any goal. `change U` replaces the main goal target `T` with `U`
providing that `U` is well-formed with respect to the main goal local context,
and `T` and `U` are definitionally equal.
-/
meta def change (q : qexpr0) : tactic unit :=
i_to_expr q >>= tactic.change

/--
This tactic applies to any goal. It gives directly the exact proof
term of the goal. Let `T` be our goal, let `p` be a term of type `U` then
`exact p` succeeds iff `T` and `U` are definitionally equal.
-/
meta def exact (q : qexpr0) : tactic unit :=
do tgt : expr ← target,
   i_to_expr_strict `(%%q : %%tgt) >>= tactic.exact

private meta def get_locals : list name → tactic (list expr)
| []      := return []
| (n::ns) := do h ← get_local n, hs ← get_locals ns, return (h::hs)

/--
`revert h₁ ... hₙ` applies to any goal with hypotheses `h₁` ... `hₙ`.
It moves the hypotheses and its dependencies to the goal target.
This tactic is the inverse of `intro`.
-/
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

private meta def resolve_name' (n : name) : tactic expr :=
do {
  e ← resolve_name n,
  match e with
  | expr.const n _           := mk_const n -- create metavars for universe levels
  | _                        := return e
  end
}

/- Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/
private meta def to_expr' (p : pexpr) : tactic expr :=
let e := pexpr.to_raw_expr p in
match e with
| (const c [])          := do new_e ← resolve_name' c, save_type_info new_e e, return new_e
| (local_const c _ _ _) := do new_e ← resolve_name' c, save_type_info new_e e, return new_e
| _                     := i_to_expr p
end

private meta def to_symm_expr_list : list (pexpr × pos) → tactic (list (bool × expr × pos))
| []             := return []
| ((p, pos)::ps) :=
  match is_neg p with
  | some a :=  do r ← to_expr' a, rs ← to_symm_expr_list ps, return ((tt, r, pos) :: rs)
  | none   :=  do r ← to_expr' p, rs ← to_symm_expr_list ps, return ((ff, r, pos) :: rs)
  end

private meta def rw_goal : transparency → list (bool × expr × pos) → tactic unit
| m []                   := return ()
| m ((symm, e, pos)::es) := save_info pos.1 pos.2 >> rewrite_core m tt tt occurrences.all symm e >> rw_goal m es

private meta def rw_hyp : transparency → list (bool × expr × pos) → name → tactic unit
| m []              hname := return ()
| m ((symm, e, pos)::es) hname :=
  do h ← get_local hname,
     save_info pos.1 pos.2,
     rewrite_at_core m tt tt occurrences.all symm e h,
     rw_hyp m es hname

private meta def rw_hyps : transparency → list (bool × expr × pos) → list name → tactic unit
| m es  []      := return ()
| m es  (h::hs) := rw_hyp m es h >> rw_hyps m es hs

private meta def rw_core (m : transparency) (hs : qexpr_list_or_qexpr0_with_pos) (loc : location) : tactic unit :=
do hlist ← to_symm_expr_list hs,
   match loc with
   | [] := rw_goal m hlist >> try (reflexivity reducible)
   | hs := rw_hyps m hlist hs >> try (reflexivity reducible)
   end

meta def rewrite : qexpr_list_or_qexpr0_with_pos → location → tactic unit :=
rw_core reducible

meta def rw : qexpr_list_or_qexpr0_with_pos → location → tactic unit :=
rewrite

/- rewrite followed by assumption -/
meta def rwa (q : qexpr_list_or_qexpr0_with_pos) (l : location) : tactic unit :=
rewrite q l >> try assumption

meta def erewrite : qexpr_list_or_qexpr0_with_pos → location → tactic unit :=
rw_core semireducible

meta def erw : qexpr_list_or_qexpr0_with_pos → location → tactic unit :=
erewrite

private meta def get_type_name (e : expr) : tactic name :=
do e_type ← infer_type e >>= whnf,
   (const I ls) ← return $ get_app_fn e_type,
   return I

meta def induction (p : qexpr0) (rec_name : using_ident) (ids : with_ident_list) : tactic unit :=
do e ← i_to_expr p,
   match rec_name with
   | some n := tactic.induction e n ids
   | none   := do I ← get_type_name e, tactic.induction e (I <.> "rec") ids
   end,
   return ()

meta def cases (p : qexpr0) (ids : with_ident_list) : tactic unit :=
do e ← i_to_expr p,
   tactic.cases e ids

meta def destruct (p : qexpr0) : tactic unit :=
do e ← i_to_expr p, tactic.destruct e

meta def generalize (p : qexpr) (x : ident) : tactic unit :=
do e ← i_to_expr p,
   tactic.generalize e x

meta def trivial : tactic unit :=
tactic.triv <|> tactic.reflexivity <|> tactic.contradiction <|> fail "trivial tactic failed"

/-- Closes the main goal using sorry. -/
meta def admit : tactic unit := tactic.admit

/--
This tactic applies to any goal. The contradiction tactic attempts to find in the current local context an hypothesis that is equivalent to
an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors,
or two contradictory hypotheses.
-/
meta def contradiction : tactic unit :=
tactic.contradiction

meta def repeat : itactic → tactic unit :=
tactic.repeat

meta def try : itactic → tactic unit :=
tactic.try

meta def solve1 : itactic → tactic unit :=
tactic.solve1

meta def abstract (id : opt_ident) (tac : irtactic) : tactic unit :=
tactic.abstract tac id

meta def all_goals : itactic → tactic unit :=
tactic.all_goals

meta def any_goals : itactic → tactic unit :=
tactic.any_goals

meta def focus (tac : irtactic) : tactic unit :=
tactic.focus [tac]

/--
This tactic applies to any goal. `assert h : T` adds a new hypothesis of name `h` and type `T` to the current goal and opens a new subgoal with target `T`.
The new subgoal becomes the main goal.
-/
meta def assert (h : ident) (c : colon_tk) (q : qexpr0) : tactic unit :=
do e ← i_to_expr_strict q,
   tactic.assert h e

meta def define (h : ident) (c : colon_tk) (q : qexpr0) : tactic unit :=
do e ← i_to_expr_strict q,
   tactic.define h e

/--
This tactic applies to any goal. `assertv h : T := p` adds a new hypothesis of name `h` and type `T` to the current goal if `p` a term of type `T`.
-/
meta def assertv (h : ident) (c : colon_tk) (q₁ : qexpr0) (a : assign_tk) (q₂ : qexpr0) : tactic unit :=
do t ← i_to_expr_strict q₁,
   v ← i_to_expr_strict `(%%q₂ : %%t),
   tactic.assertv h t v

meta def definev (h : ident) (c : colon_tk) (q₁ : qexpr0) (a : assign_tk) (q₂ : qexpr0) : tactic unit :=
do t ← i_to_expr_strict q₁,
   v ← i_to_expr_strict `(%%q₂ : %%t),
   tactic.definev h t v

meta def note (h : ident) (a : assign_tk) (q : qexpr0) : tactic unit :=
do p ← i_to_expr_strict q,
   tactic.note h p

meta def pose (h : ident) (a : assign_tk) (q : qexpr0) : tactic unit :=
do p ← i_to_expr_strict q,
   tactic.pose h p

/--
This tactic displays the current state in the tracing buffer.
-/
meta def trace_state : tactic unit :=
tactic.trace_state

/--
`trace a` displays `a` in the tracing buffer.
-/
meta def trace {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
tactic.trace a

meta def existsi (e : qexpr0) : tactic unit :=
i_to_expr e >>= tactic.existsi

/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`).
It tries to apply each constructor of `I` until it succeeds.
-/
meta def constructor : tactic unit :=
tactic.constructor

meta def left : tactic unit :=
tactic.left

meta def right : tactic unit :=
tactic.right

meta def split : tactic unit :=
tactic.split

meta def exfalso : tactic unit :=
tactic.exfalso

/--
The injection tactic is based on the fact that constructors of inductive datatypes are injections.
That means that if `c` is a constructor of an inductive datatype,
and if `(c t₁)` and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.

If `q` is a proof of a statement of conclusion `t₁ = t₂`,
then injection applies injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in the same positions.
For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`.
To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.

Given `h : a::b = c::d`, the tactic `injection h` adds to new hypothesis with types `a = c` and `b = d`
to the main goal. The tactic `injection h with h₁ h₂` uses the names `h₁` an `h₂` to name the new
hypotheses.
-/
meta def injection (q : qexpr0) (hs : with_ident_list) : tactic unit :=
do e ← i_to_expr q, tactic.injection_with e hs

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s^.add_simp n, add_simps s' ns

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail ("invalid simplification lemma '" ++ to_string n ++ "' (use command 'set_option trace.simp_lemmas true' for more details)")

private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (n : name) (ref : expr) : tactic simp_lemmas :=
do
  e ← resolve_name n,
  match e with
  | expr.const n _           :=
    (do b ← is_valid_simp_lemma_cnst reducible n, guard b, save_const_type_info n ref, s^.add_simp n)
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns^.length > 0), save_const_type_info n ref, add_simps s eqns)
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do b ← is_valid_simp_lemma reducible e, guard b, try (save_type_info e ref), s^.add e)
    <|>
    report_invalid_simp_lemma n
  end

private meta def simp_lemmas.add_pexpr (s : simp_lemmas) (p : pexpr) : tactic simp_lemmas :=
let e := pexpr.to_raw_expr p in
match e with
| (const c [])          := simp_lemmas.resolve_and_add s c e
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s c e
| _                     := do new_e ← i_to_expr p, s^.add new_e
end

private meta def simp_lemmas.append_pexprs : simp_lemmas → list pexpr → tactic simp_lemmas
| s []      := return s
| s (l::ls) := do new_s ← simp_lemmas.add_pexpr s l, simp_lemmas.append_pexprs new_s ls

private meta def mk_simp_set (attr_names : list name) (hs : list qexpr) (ex : list name) : tactic simp_lemmas :=
do s₀ ← join_user_simp_lemmas attr_names,
   s₁ ← simp_lemmas.append_pexprs s₀ hs,
   return $ simp_lemmas.erase s₁ ex

private meta def simp_goal (cfg : simplify_config) : simp_lemmas → tactic unit
| s := do
   (new_target, Heq) ← target >>= simplify_core cfg s `eq,
   tactic.assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_eq_mpr Heq Ht >>= tactic.exact

private meta def simp_hyp (cfg : simplify_config) (s : simp_lemmas) (h_name : name) : tactic unit :=
do h     ← get_local h_name,
   htype ← infer_type h,
   (new_htype, eqpr) ← simplify_core cfg s `eq htype,
   tactic.assert (expr.local_pp_name h) new_htype,
   mk_eq_mp eqpr h >>= tactic.exact,
   try $ tactic.clear h

private meta def simp_hyps (cfg : simplify_config) : simp_lemmas → location → tactic unit
| s []      := skip
| s (h::hs) := simp_hyp cfg s h >> simp_hyps s hs

private meta def simp_core (cfg : simplify_config) (ctx : list expr) (hs : opt_qexpr_list) (attr_names : with_ident_list) (ids : without_ident_list) (loc : location) : tactic unit :=
do s ← mk_simp_set attr_names hs ids,
   s ← s^.append ctx,
   match loc : _ → tactic unit with
   | [] := simp_goal cfg s
   | _  := simp_hyps cfg s loc
   end,
   try tactic.triv, try (tactic.reflexivity reducible)

/--
This tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses.
It has many variants.

- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

- `simp [h_1, ..., h_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `h_i`s.
   The `h_i`'s are terms. If a `h_i` is a definition `f`, then the equational lemmas associated with `f` are used.
   This is a convenient way to "unfold" `f`.

- `simp without id_1 ... id_n` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`,
   but removes the ones named `id_i`s.

- `simp at h` simplifies the non dependent hypothesis `h : T`. The tactic fails if the target or another hypothesis depends on `h`.

- `simp with attr` simplifies the main goal target using the lemmas tagged with the attribute `[attr]`.
-/
meta def simp (hs : opt_qexpr_list) (attr_names : with_ident_list) (ids : without_ident_list) (loc : location) : tactic unit :=
simp_core {} [] hs attr_names ids loc

/--
Similar to the `simp` tactic, but uses contextual simplification. For example, when simplifying `t = s → p`,
the equation `t = s` is automatically added to the set of simplification rules when simplifying `p`.
-/
meta def ctx_simp (hs : opt_qexpr_list) (attr_names : with_ident_list) (ids : without_ident_list) (loc : location) : tactic unit :=
simp_core {contextual := tt} [] hs attr_names ids loc

/--
Similar to the `simp` tactic, but adds all applicable hypotheses as simplification rules.
-/
meta def simp_using_hs (hs : opt_qexpr_list) (attr_names : with_ident_list) (ids : without_ident_list) : tactic unit :=
do ctx ← collect_ctx_simps,
   simp_core {} ctx hs attr_names ids []

private meta def dsimp_hyps (s : simp_lemmas) : location → tactic unit
| []      := skip
| (h::hs) := get_local h >>= dsimp_at_core s

meta def dsimp (es : opt_qexpr_list) (attr_names : with_ident_list) (ids : without_ident_list) : location → tactic unit
| [] := do s ← mk_simp_set attr_names es ids, tactic.dsimp_core s
| hs := do s ← mk_simp_set attr_names es ids, dsimp_hyps s hs

/--
This tactic applies to a goal that has the form `t ~ u` where `~` is a reflexive relation.
That is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`.
The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
meta def reflexivity : tactic unit :=
tactic.reflexivity

/--
Shorter name for the tactic `reflexivity`.
-/
meta def refl : tactic unit :=
tactic.reflexivity

meta def symmetry : tactic unit :=
tactic.symmetry

meta def transitivity : tactic unit :=
tactic.transitivity

meta def ac_reflexivity : tactic unit :=
tactic.ac_refl

meta def ac_refl : tactic unit :=
tactic.ac_refl

meta def cc : tactic unit :=
tactic.cc

meta def subst (q : qexpr0) : tactic unit :=
i_to_expr q >>= tactic.subst >> try (tactic.reflexivity reducible)

meta def clear : raw_ident_list → tactic unit :=
tactic.clear_lst

private meta def to_qualified_name_core : name → list name → tactic name
| n []        := fail $ "unknown declaration '" ++ to_string n ++ "'"
| n (ns::nss) := do
  curr ← return $ ns ++ n,
  env  ← get_env,
  if env^.contains curr then return curr
  else to_qualified_name_core n nss

private meta def to_qualified_name (n : name) : tactic name :=
do env ← get_env,
   if env^.contains n then return n
   else do
     ns ← open_namespaces,
     to_qualified_name_core n ns

private meta def to_qualified_names : list name → tactic (list name)
| []      := return []
| (c::cs) := do new_c ← to_qualified_name c, new_cs ← to_qualified_names cs, return (new_c::new_cs)

private meta def dunfold_hyps : list name → location → tactic unit
| cs []      := skip
| cs (h::hs) := get_local h >>= dunfold_at cs >> dunfold_hyps cs hs

meta def dunfold : raw_ident_list → location → tactic unit
| cs [] := do new_cs ← to_qualified_names cs, tactic.dunfold new_cs
| cs hs := do new_cs ← to_qualified_names cs, dunfold_hyps new_cs hs

/- TODO(Leo): add support for non-refl lemmas -/
meta def unfold : raw_ident_list → location → tactic unit :=
dunfold

private meta def dunfold_hyps_occs : name → occurrences → location → tactic unit
| c occs []  := skip
| c occs (h::hs) := get_local h >>= dunfold_core_at occs [c] >> dunfold_hyps_occs c occs hs

meta def dunfold_occs : ident → list nat → location → tactic unit
| c ps [] := do new_c ← to_qualified_name c, tactic.dunfold_occs_of ps new_c
| c ps hs := do new_c ← to_qualified_name c, dunfold_hyps_occs new_c (occurrences.pos ps) hs

/- TODO(Leo): add support for non-refl lemmas -/
meta def unfold_occs : ident → list nat → location → tactic unit :=
dunfold_occs

private meta def delta_hyps : list name → location → tactic unit
| cs []      := skip
| cs (h::hs) := get_local h >>= delta_at cs >> dunfold_hyps cs hs

meta def delta : raw_ident_list → location → tactic unit
| cs [] := do new_cs ← to_qualified_names cs, tactic.delta new_cs
| cs hs := do new_cs ← to_qualified_names cs, delta_hyps new_cs hs

end interactive
end tactic

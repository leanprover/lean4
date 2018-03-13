/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.category
import init.meta.simp_tactic
import init.meta.smt.congruence_closure
import init.meta.smt.ematch

universe u

run_cmd mk_simp_attr `pre_smt
run_cmd mk_hinst_lemma_attr_set `ematch [] [`ematch_lhs]

/--
  Configuration for the smt tactic preprocessor. The preprocessor
  is applied whenever a new hypothesis is introduced.

  - simp_attr: is the attribute name for the simplification lemmas
    that are used during the preprocessing step.

  - max_steps: it is the maximum number of steps performed by the simplifier.

  - zeta: if tt, then zeta reduction (i.e., unfolding let-expressions)
    is used during preprocessing.
-/
structure smt_pre_config :=
(simp_attr : name := `pre_smt)
(max_steps : nat  := 1000000)
(zeta      : bool := ff)

/--
Configuration for the smt_state object.

- em_attr: is the attribute name for the hinst_lemmas
  that are used for ematching -/
structure smt_config :=
(cc_cfg        : cc_config      := {})
(em_cfg        : ematch_config  := {})
(pre_cfg       : smt_pre_config := {})
(em_attr       : name           := `ematch)

meta def smt_config.set_classical (c : smt_config) (b : bool) : smt_config :=
{ cc_cfg := { em := b, ..c.cc_cfg }, ..c }

meta constant smt_goal                  : Type
meta def smt_state :=
list smt_goal
meta constant smt_state.mk              : smt_config → tactic smt_state
meta constant smt_state.to_format       : smt_state → tactic_state → format
/-- Return tt iff classical excluded middle was enabled at  smt_state.mk -/
meta constant smt_state.classical       : smt_state → bool

meta def smt_tactic :=
state_t smt_state tactic

meta instance : has_append smt_state :=
list.has_append

section
local attribute [reducible] smt_tactic
meta instance : monad smt_tactic := by apply_instance
meta instance : alternative smt_tactic := by apply_instance
meta instance : monad_state smt_state smt_tactic := by apply_instance
end

/- We don't use the default state_t lift operation because only
   tactics that do not change hypotheses can be automatically lifted to smt_tactic. -/
meta constant tactic_to_smt_tactic (α : Type) : tactic α → smt_tactic α

meta instance : has_monad_lift tactic smt_tactic :=
⟨tactic_to_smt_tactic⟩

meta instance (α : Type) : has_coe (tactic α) (smt_tactic α) :=
⟨monad_lift⟩

meta instance : monad_fail smt_tactic :=
{ fail := λ α s, (tactic.fail (to_fmt s) : smt_tactic α), ..smt_tactic.monad }

namespace smt_tactic
open tactic (transparency)
meta constant intros                     : smt_tactic unit
meta constant intron                     : nat  → smt_tactic unit
meta constant intro_lst                  : list name → smt_tactic unit
/--
  Try to close main goal by using equalities implied by the congruence
  closure module.
-/
meta constant close                           : smt_tactic unit
/--
  Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from lemmas in the main goal with terms
  in the main goal. The set of lemmas is populated with theorems
  tagged with the attribute specified at smt_config.em_attr, and lemmas
  added using tactics such as `smt_tactic.add_lemmas`.
  The current set of lemmas can be retrieved using the tactic `smt_tactic.get_lemmas`.

  Remark: the given predicate is applied to every new instance. The instance
  is only added to the state if the predicate returns tt.
-/
meta constant ematch_core                     : (expr → bool) → smt_tactic unit
/--
  Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from the given lemmas with terms in
  the main goal.
-/
meta constant ematch_using                    : hinst_lemmas → smt_tactic unit
meta constant mk_ematch_eqn_lemmas_for_core   : transparency → name → smt_tactic hinst_lemmas
meta constant to_cc_state                     : smt_tactic cc_state
meta constant to_em_state                     : smt_tactic ematch_state
meta constant get_config                      : smt_tactic smt_config
/--
  Preprocess the given term using the same simplifications rules used when
  we introduce a new hypothesis. The result is pair containing the resulting
  term and a proof that it is equal to the given one.
-/
meta constant preprocess                      : expr → smt_tactic (expr × expr)
meta constant get_lemmas                      : smt_tactic hinst_lemmas
meta constant set_lemmas                      : hinst_lemmas → smt_tactic unit
meta constant add_lemmas                      : hinst_lemmas → smt_tactic unit

meta def add_ematch_lemma_core (md : transparency) (as_simp : bool) (e : expr) : smt_tactic unit :=
do h  ← hinst_lemma.mk_core md e as_simp,
   add_lemmas (mk_hinst_singleton h)

meta def add_ematch_lemma_from_decl_core (md : transparency) (as_simp : bool) (n : name) : smt_tactic unit :=
do h  ← hinst_lemma.mk_from_decl_core md n as_simp,
   add_lemmas (mk_hinst_singleton h)

meta def add_ematch_eqn_lemmas_for_core  (md : transparency) (n : name) : smt_tactic unit :=
do hs ← mk_ematch_eqn_lemmas_for_core md n,
   add_lemmas hs

meta def ematch : smt_tactic unit :=
ematch_core (λ _, tt)

meta def failed {α} : smt_tactic α :=
tactic.failed

meta def fail {α : Type} {β : Type u} [has_to_format β] (msg : β) : smt_tactic α :=
tactic.fail msg

meta def try {α : Type} (t : smt_tactic α) : smt_tactic unit :=
⟨λ ss ts, result.cases_on (t.run ss ts)
 (λ ⟨a, new_ss⟩, result.success ((), new_ss))
 (λ e ref s', result.success ((), ss) ts)⟩

/-- `iterate_at_most n t`: repeat the given tactic at most n times or until t fails -/
meta def iterate_at_most : nat → smt_tactic unit → smt_tactic unit
| 0     t := return ()
| (n+1) t := (do t, iterate_at_most n t) <|> return ()

/-- `iterate_exactly n t` : execute t n times -/
meta def iterate_exactly : nat → smt_tactic unit → smt_tactic unit
| 0     t := return ()
| (n+1) t := do t, iterate_exactly n t

meta def iterate : smt_tactic unit → smt_tactic unit :=
iterate_at_most 100000

meta def eblast : smt_tactic unit :=
iterate (ematch >> try close)

open tactic

protected meta def read : smt_tactic (smt_state × tactic_state) :=
do s₁ ← get,
   s₂ ← tactic.read,
   return (s₁, s₂)

protected meta def write : smt_state × tactic_state → smt_tactic unit :=
λ ⟨ss, ts⟩, ⟨λ _ _, result.success ((), ss) ts⟩

private meta def mk_smt_goals_for (cfg : smt_config) : list expr → list smt_goal → list expr
                                  → tactic (list smt_goal × list expr)
| []        sr tr := return (sr.reverse, tr.reverse)
| (tg::tgs) sr tr := do
  tactic.set_goals [tg],
  [new_sg] ← smt_state.mk cfg | tactic.failed,
  [new_tg] ← get_goals | tactic.failed,
  mk_smt_goals_for tgs (new_sg::sr) (new_tg::tr)

/- See slift -/
meta def slift_aux {α : Type} (t : tactic α) (cfg : smt_config) : smt_tactic α :=
⟨λ ss, do
   _::sgs  ← return ss | tactic.fail "slift tactic failed, there no smt goals to be solved",
   tg::tgs ← tactic.get_goals | tactic.failed,
   tactic.set_goals [tg], a ← t,
   new_tgs ← tactic.get_goals,
   (new_sgs, new_tgs) ← mk_smt_goals_for cfg new_tgs [] [],
   tactic.set_goals (new_tgs ++ tgs),
   return (a, new_sgs ++ sgs)⟩

/--
  This lift operation will restart the SMT state.
  It is useful for using tactics that change the set of hypotheses. -/
meta def slift {α : Type} (t : tactic α) : smt_tactic α :=
get_config >>= slift_aux t

meta def trace_state : smt_tactic unit :=
do (s₁, s₂) ← smt_tactic.read,
   trace (smt_state.to_format s₁ s₂)

meta def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic unit :=
tactic.trace a

meta def to_expr (q : pexpr) (allow_mvars := tt) : smt_tactic expr :=
tactic.to_expr q allow_mvars

meta def classical : smt_tactic bool :=
do s ← get,
   return s.classical

meta def num_goals : smt_tactic nat :=
list.length <$> get

/- Low level primitives for managing set of goals -/
meta def get_goals : smt_tactic (list smt_goal × list expr) :=
do (g₁, _) ← smt_tactic.read,
   g₂ ← tactic.get_goals,
   return (g₁, g₂)

meta def set_goals : list smt_goal → list expr → smt_tactic unit :=
λ g₁ g₂, ⟨λ ss, tactic.set_goals g₂ >> return ((), g₁)⟩

private meta def all_goals_core (tac : smt_tactic unit) : list smt_goal → list expr → list smt_goal → list expr → smt_tactic unit
| []        ts        acs act := set_goals acs (ts ++ act)
| (s :: ss) []        acs act := fail "ill-formed smt_state"
| (s :: ss) (t :: ts) acs act :=
  do set_goals [s] [t],
     tac,
     (new_ss, new_ts) ← get_goals,
     all_goals_core ss ts (acs ++ new_ss) (act ++ new_ts)

/-- Apply the given tactic to all goals. -/
meta def all_goals (tac : smt_tactic unit) : smt_tactic unit :=
do (ss, ts) ← get_goals,
   all_goals_core tac ss ts [] []

/-- LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
meta def seq (tac1 : smt_tactic unit) (tac2 : smt_tactic unit) : smt_tactic unit :=
do (s::ss, t::ts) ← get_goals,
   set_goals [s] [t],
   tac1, all_goals tac2,
   (new_ss, new_ts) ← get_goals,
   set_goals (new_ss ++ ss) (new_ts ++ ts)

meta instance : has_andthen (smt_tactic unit) (smt_tactic unit) (smt_tactic unit) :=
⟨seq⟩

meta def focus1 {α} (tac : smt_tactic α) : smt_tactic α :=
do (s::ss, t::ts) ← get_goals,
   match ss with
   | []  := tac
   | _   := do
     set_goals [s] [t],
     a ← tac,
     (ss', ts') ← get_goals,
     set_goals (ss' ++ ss) (ts' ++ ts),
     return a
   end

meta def solve1 (tac : smt_tactic unit) : smt_tactic unit :=
do (ss, gs) ← get_goals,
   match ss, gs with
   | [],     _    := fail "solve1 tactic failed, there isn't any goal left to focus"
   | _,     []    := fail "solve1 tactic failed, there isn't any smt goal left to focus"
   | s::ss, g::gs :=
     do set_goals [s] [g],
        tac,
        (ss', gs') ← get_goals,
        match ss', gs' with
        | [], [] := set_goals ss gs
        | _,  _  := fail "solve1 tactic failed, focused goal has not been solved"
        end
   end

meta def swap : smt_tactic unit :=
do (ss, ts) ← get_goals,
   match ss, ts with
   | (s₁ :: s₂ :: ss), (t₁ :: t₂ :: ts) := set_goals (s₂ :: s₁ :: ss) (t₂ :: t₁ :: ts)
   | _,                _                := failed
   end

/-- Add a new goal for t, and the hypothesis (h : t) in the current goal. -/
meta def assert (h : name) (t : expr) : smt_tactic unit :=
tactic.assert_core h t >> swap >> intros >> swap >> try close

/-- Add the hypothesis (h : t) in the current goal if v has type t. -/
meta def assertv (h : name) (t : expr) (v : expr) : smt_tactic unit :=
tactic.assertv_core h t v >> intros >> return ()

/-- Add a new goal for t, and the hypothesis (h : t := ?M) in the current goal. -/
meta def define  (h : name) (t : expr) : smt_tactic unit :=
tactic.define_core h t >> swap >> intros >> swap >> try close

/-- Add the hypothesis (h : t := v) in the current goal if v has type t. -/
meta def definev (h : name) (t : expr) (v : expr) : smt_tactic unit :=
tactic.definev_core h t v >> intros >> return ()

/-- Add (h : t := pr) to the current goal -/
meta def pose (h : name) (t : option expr := none) (pr : expr) : smt_tactic unit :=
match t with
| none   := do t ← infer_type pr, definev h t pr
| some t := definev h t pr
end

/-- Add (h : t) to the current goal, given a proof (pr : t) -/
meta def note (h : name) (t : option expr := none) (pr : expr) : smt_tactic unit :=
match t with
| none   := do t ← infer_type pr, assertv h t pr
| some t := assertv h t pr
end

meta def destruct (e : expr) : smt_tactic unit :=
smt_tactic.seq (tactic.destruct e) smt_tactic.intros

meta def by_cases (e : expr) : smt_tactic unit :=
do c ← classical,
   if c then
     destruct (expr.app (expr.const `classical.em []) e)
   else do
     dec_e ← (mk_app `decidable [e] <|> fail "by_cases smt_tactic failed, type is not a proposition"),
     inst  ← (mk_instance dec_e <|> fail "by_cases smt_tactic failed, type of given expression is not decidable"),
     em    ← mk_app `decidable.em [e, inst],
     destruct em

meta def by_contradiction : smt_tactic unit :=
do t ← target,
   c ← classical,
   if t.is_false then skip
   else if c then do
      apply (expr.app (expr.const `classical.by_contradiction []) t),
      intros
   else do
     dec_t ← (mk_app `decidable [t] <|> fail "by_contradiction smt_tactic failed, target is not a proposition"),
     inst  ← (mk_instance dec_t <|> fail "by_contradiction smt_tactic failed, target is not decidable"),
     a     ← mk_mapp `decidable.by_contradiction [some t, some inst],
     apply a,
     intros

/-- Return a proof for e, if 'e' is a known fact in the main goal. -/
meta def proof_for (e : expr) : smt_tactic expr :=
do cc ← to_cc_state, cc.proof_for e

/-- Return a refutation for e (i.e., a proof for (not e)), if 'e' has been refuted in the main goal. -/
meta def refutation_for (e : expr) : smt_tactic expr :=
do cc ← to_cc_state, cc.refutation_for e

meta def get_facts : smt_tactic (list expr) :=
do cc ← to_cc_state,
   return $ cc.eqc_of expr.mk_true

meta def get_refuted_facts : smt_tactic (list expr) :=
do cc ← to_cc_state,
   return $ cc.eqc_of expr.mk_false

meta def add_ematch_lemma : expr → smt_tactic unit :=
add_ematch_lemma_core reducible ff

meta def add_ematch_lhs_lemma : expr → smt_tactic unit :=
add_ematch_lemma_core reducible tt

meta def add_ematch_lemma_from_decl : name → smt_tactic unit :=
add_ematch_lemma_from_decl_core reducible ff

meta def add_ematch_lhs_lemma_from_decl : name → smt_tactic unit :=
add_ematch_lemma_from_decl_core reducible ff

meta def add_ematch_eqn_lemmas_for : name → smt_tactic unit :=
add_ematch_eqn_lemmas_for_core reducible

meta def add_lemmas_from_facts_core : list expr → smt_tactic unit
| []      := return ()
| (f::fs) := do
  try (is_prop f >> guard (f.is_pi && bnot (f.is_arrow)) >> proof_for f >>= add_ematch_lemma_core reducible ff),
  add_lemmas_from_facts_core fs

meta def add_lemmas_from_facts : smt_tactic unit :=
get_facts >>= add_lemmas_from_facts_core

meta def induction (e : expr) (ids : list name := []) (rec : option name := none) : smt_tactic unit :=
slift (tactic.induction e ids rec >> return ()) -- pass on the information?

meta def when (c : Prop) [decidable c] (tac : smt_tactic unit) : smt_tactic unit :=
if c then tac else skip

meta def when_tracing (n : name) (tac : smt_tactic unit) : smt_tactic unit :=
when (is_trace_enabled_for n = tt) tac

end smt_tactic

open smt_tactic

meta def using_smt {α} (t : smt_tactic α) (cfg : smt_config := {}) : tactic α :=
do ss ← smt_state.mk cfg,
   (a, _) ← (do a ← t, iterate close, return a).run ss,
   return a

meta def using_smt_with {α} (cfg : smt_config) (t : smt_tactic α) : tactic α :=
using_smt t cfg

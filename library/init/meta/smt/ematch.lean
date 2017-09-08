/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.congruence_closure
import init.meta.attribute init.meta.simp_tactic
import init.meta.interactive_base init.meta.derive
open tactic

/-- Heuristic instantiation lemma -/
meta constant hinst_lemma : Type

meta constant hinst_lemmas : Type

/-- `mk_core m e as_simp`, m is used to decide which definitions will be unfolded in patterns.
   If as_simp is tt, then this tactic will try to use the left-hand-side of the conclusion
   as a pattern. -/
meta constant hinst_lemma.mk_core           : transparency → expr → bool → tactic hinst_lemma
meta constant hinst_lemma.mk_from_decl_core : transparency → name → bool → tactic hinst_lemma
meta constant hinst_lemma.pp                : hinst_lemma → tactic format
meta constant hinst_lemma.id                : hinst_lemma → name

meta instance : has_to_tactic_format hinst_lemma :=
⟨hinst_lemma.pp⟩

meta def hinst_lemma.mk (h : expr) : tactic hinst_lemma :=
hinst_lemma.mk_core reducible h ff

meta def hinst_lemma.mk_from_decl (h : name) : tactic hinst_lemma :=
hinst_lemma.mk_from_decl_core reducible h ff

meta constant hinst_lemmas.mk              : hinst_lemmas
meta constant hinst_lemmas.add             : hinst_lemmas → hinst_lemma → hinst_lemmas
meta constant hinst_lemmas.fold {α : Type} : hinst_lemmas → α → (hinst_lemma → α → α) → α
meta constant hinst_lemmas.merge           : hinst_lemmas → hinst_lemmas → hinst_lemmas

meta def mk_hinst_singleton : hinst_lemma → hinst_lemmas :=
hinst_lemmas.add hinst_lemmas.mk

meta def hinst_lemmas.pp (s : hinst_lemmas) : tactic format :=
let tac := s.fold (return format.nil)
    (λ h tac, do
      hpp ← h.pp,
      r   ← tac,
      if r.is_nil then return hpp
      else return format!"{r},\n{hpp}")
in do
  r ← tac,
  return $ format.cbrace (format.group r)

meta instance : has_to_tactic_format hinst_lemmas :=
⟨hinst_lemmas.pp⟩

open tactic

private meta def add_lemma (m : transparency) (as_simp : bool) (h : name) (hs : hinst_lemmas) : tactic hinst_lemmas :=
do h ← hinst_lemma.mk_from_decl_core m h as_simp, return $ hs.add h

meta def to_hinst_lemmas_core (m : transparency) : bool → list name → hinst_lemmas → tactic hinst_lemmas
| as_simp []      hs := return hs
| as_simp (n::ns) hs :=
  let add n := add_lemma m as_simp n hs >>= to_hinst_lemmas_core as_simp ns
  in do
  /- First check if n is the name of a function with equational lemmas associated with it -/
  eqns   ← tactic.get_eqn_lemmas_for tt n,
  match eqns with
  | []  := do
    /- n is not the name of a function definition or it does not have equational lemmas, then check if it is a lemma -/
    add n
  | _   := do
    p ← is_prop_decl n,
    if p then add n /- n is a proposition -/
    else do
      /- Add equational lemmas to resulting hinst_lemmas -/
      new_hs ← to_hinst_lemmas_core tt eqns hs,
      to_hinst_lemmas_core as_simp ns new_hs
  end

meta def mk_hinst_lemma_attr_core (attr_name : name) (as_simp : bool) : command :=
do let t := `(user_attribute hinst_lemmas),
   let v := `({name     := attr_name,
               descr    := "hinst_lemma attribute",
               after_set := some $ λ n _ _,
                 to_hinst_lemmas_core reducible as_simp [n] hinst_lemmas.mk >> skip <|>
                 fail format!"invalid ematch lemma '{n}'",
               -- allow unsetting
               before_unset := some $ λ _ _, skip,
               cache_cfg := {
                 mk_cache := λ ns, to_hinst_lemmas_core reducible as_simp ns hinst_lemmas.mk,
                 dependencies := [`reducibility]}} : user_attribute hinst_lemmas),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def mk_hinst_lemma_attrs_core (as_simp : bool) : list name → command
| []      := skip
| (n::ns) :=
  (mk_hinst_lemma_attr_core n as_simp >> mk_hinst_lemma_attrs_core ns)
  <|>
  (do type ← infer_type (expr.const n []),
      let expected := `(user_attribute),
      (is_def_eq type expected
       <|> fail format!"failed to create hinst_lemma attribute '{n}', declaration already exists and has different type."),
      mk_hinst_lemma_attrs_core ns)

meta def merge_hinst_lemma_attrs (m : transparency) (as_simp : bool) : list name → hinst_lemmas → tactic hinst_lemmas
| []            hs := return hs
| (attr::attrs) hs := do
  ns     ← attribute.get_instances attr,
  new_hs ← to_hinst_lemmas_core m as_simp ns hs,
  merge_hinst_lemma_attrs attrs new_hs

/--
Create a new "cached" attribute (attr_name : user_attribute hinst_lemmas).
It also creates "cached" attributes for each attr_names and simp_attr_names if they have not been defined
yet. Moreover, the hinst_lemmas for attr_name will be the union of the lemmas tagged with
    attr_name, attrs_name, and simp_attr_names.
For the ones in simp_attr_names, we use the left-hand-side of the conclusion as the pattern.
-/
meta def mk_hinst_lemma_attr_set (attr_name : name) (attr_names : list name) (simp_attr_names : list name) : command :=
do mk_hinst_lemma_attrs_core ff attr_names,
   mk_hinst_lemma_attrs_core tt simp_attr_names,
   let t  := `(user_attribute hinst_lemmas),
   let v  := `({name     := attr_name,
                descr    := "hinst_lemma attribute set",
                after_set := some $ λ n _ _,
                  to_hinst_lemmas_core reducible ff [n] hinst_lemmas.mk >> skip <|>
                  fail format!"invalid ematch lemma '{n}'",
                -- allow unsetting
                before_unset := some $ λ _ _, skip,
                cache_cfg := {
                  mk_cache := λ ns, do {
                    hs₁ ← to_hinst_lemmas_core reducible ff ns hinst_lemmas.mk,
                    hs₂ ← merge_hinst_lemma_attrs reducible ff attr_names hs₁,
                    merge_hinst_lemma_attrs reducible tt simp_attr_names hs₂},
                  dependencies := [`reducibility] ++ attr_names ++ simp_attr_names}} : user_attribute hinst_lemmas),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def get_hinst_lemmas_for_attr (attr_name : name) : tactic hinst_lemmas :=
get_attribute_cache_dyn attr_name

structure ematch_config :=
(max_instances  : nat := 10000)
(max_generation : nat := 10)

/- Ematching -/
meta constant ematch_state             : Type
meta constant ematch_state.mk          : ematch_config → ematch_state
meta constant ematch_state.internalize : ematch_state → expr → tactic ematch_state

namespace tactic
meta constant ematch_core       : transparency → cc_state → ematch_state → hinst_lemma → expr → tactic (list (expr × expr) × cc_state × ematch_state)
meta constant ematch_all_core   : transparency → cc_state → ematch_state → hinst_lemma → bool → tactic (list (expr × expr) × cc_state × ematch_state)

meta def ematch : cc_state → ematch_state → hinst_lemma → expr → tactic (list (expr × expr) × cc_state × ematch_state) :=
ematch_core reducible

meta def ematch_all : cc_state → ematch_state → hinst_lemma → bool → tactic (list (expr × expr) × cc_state × ematch_state) :=
ematch_all_core reducible
end tactic

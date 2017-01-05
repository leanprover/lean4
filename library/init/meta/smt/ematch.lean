/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.congruence_closure
import init.meta.attribute
open tactic

/- Heuristic instantiation lemma -/
meta constant hinst_lemma : Type

meta constant hinst_lemmas : Type

/- (mk_core m e as_simp), m is used to decide which definitions will be unfolded in patterns.
   If as_simp is tt, then this tactic will try to use the left-hand-side of the conclusion
   as a pattern. -/
meta constant hinst_lemma.mk_core           : transparency → expr → bool → tactic hinst_lemma
meta constant hinst_lemma.mk_from_decl_core : transparency → name → bool → tactic hinst_lemma
meta constant hinst_lemma.pp                : hinst_lemma → tactic format
meta constant hinst_lemma.id                : hinst_lemma → name

meta def hinst_lemma.mk (h : expr) : tactic hinst_lemma :=
hinst_lemma.mk_core reducible h ff

meta def hinst_lemma.mk_from_decl (h : name) : tactic hinst_lemma :=
hinst_lemma.mk_from_decl_core reducible h ff

meta constant hinst_lemmas.mk              : hinst_lemmas
meta constant hinst_lemmas.add             : hinst_lemmas → hinst_lemma → hinst_lemmas
meta constant hinst_lemmas.fold {α : Type} : hinst_lemmas → α → (hinst_lemma → α → α) → α

meta def hinst_lemmas.pp (s : hinst_lemmas) : tactic format :=
let tac := s^.fold (return format.nil)
    (λ h tac, do
      hpp ← h^.pp,
      r   ← tac,
      if r^.is_nil then return hpp
      else return (r ++ to_fmt "," ++ format.line ++ hpp))
in do
  r ← tac,
  return $ format.cbrace (format.group r)

open tactic

meta def to_hinst_lemmas_core (m : transparency) (as_simp : bool) : list name → hinst_lemmas → tactic hinst_lemmas
| []      hs := return hs
| (n::ns) hs := do
  h      ← hinst_lemma.mk_from_decl_core m n as_simp,
  new_hs ← return $ hs^.add h,
  to_hinst_lemmas_core ns new_hs

meta def mk_hinst_lemma_attr_core (attr_name : name) (as_simp : bool) : command :=
do t ← to_expr `(caching_user_attribute hinst_lemmas),
   a ← attr_name^.to_expr,
   b ← if as_simp then to_expr `(tt) else to_expr `(ff),
   v ← to_expr `(({ name     := %%a,
                    descr    := "hinst_lemma attribute",
                    mk_cache := λ ns, to_hinst_lemmas_core reducible %%b ns hinst_lemmas.mk,
                    dependencies := [`reducibility] } : caching_user_attribute hinst_lemmas)),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def mk_hinst_lemma_attrs_core (as_simp : bool) : list name → command
| []      := skip
| (n::ns) :=
  (mk_hinst_lemma_attr_core n as_simp >> mk_hinst_lemma_attrs_core ns)
  <|>
  (do type ← infer_type (expr.const n []),
      expected ← to_expr `(caching_user_attribute hinst_lemmas),
      (is_def_eq type expected
       <|> fail ("failed to create hinst_lemma attribute '" ++ n^.to_string ++ "', declaration already exists and has different type.")),
      mk_hinst_lemma_attrs_core ns)

meta def merge_hinst_lemma_attrs (m : transparency) (as_simp : bool) : list name → hinst_lemmas → tactic hinst_lemmas
| []            hs := return hs
| (attr::attrs) hs := do
  ns     ← attribute.get_instances attr,
  new_hs ← to_hinst_lemmas_core m as_simp ns hs,
  merge_hinst_lemma_attrs attrs new_hs

/--
Create a new "cached" attribute (attr_name : caching_user_attribute hinst_lemmas).
It also creates "cached" attributes for each attr_names and simp_attr_names if they have not been defined
yet. Moreover, the hinst_lemmas for attr_name will be the union of the lemmas tagged with
    attr_name, attrs_name, and simp_attr_names.
For the ones in simp_attr_names, we use the left-hand-side of the conclusion as the pattern.
-/
meta def mk_hinst_lemma_attr_set (attr_name : name) (attr_names : list name) (simp_attr_names : list name) : command :=
do mk_hinst_lemma_attrs_core ff attr_names,
   mk_hinst_lemma_attrs_core tt simp_attr_names,
   t  ← to_expr `(caching_user_attribute hinst_lemmas),
   a  ← attr_name^.to_expr,
   l1 : expr ← list_name.to_expr attr_names,
   l2 : expr ← list_name.to_expr simp_attr_names,
   v ← to_expr `(({ name     := %%a,
                    descr    := "hinst_lemma attribute set",
                    mk_cache := λ ns,
                      let aux1 : list name := %%l1,
                          aux2 : list name := %%l2 in
                      do {
                      hs₁ ← to_hinst_lemmas_core reducible ff ns hinst_lemmas.mk,
                      hs₂ ← merge_hinst_lemma_attrs reducible ff aux1 hs₁,
                      merge_hinst_lemma_attrs reducible tt aux2 hs₂},
                    dependencies := [`reducibility] ++ %%l1 ++ %%l2 } : caching_user_attribute hinst_lemmas)),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def get_hinst_lemmas_for_attr (attr_name : name) : tactic hinst_lemmas :=
do
  cnst   ← return (expr.const attr_name []),
  attr   ← eval_expr (caching_user_attribute hinst_lemmas) cnst,
  caching_user_attribute.get_cache attr

structure ematch_config :=
(max_instances : nat)

def default_ematch_config : ematch_config :=
{max_instances := 10000}

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

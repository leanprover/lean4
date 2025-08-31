/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
public import Std.Tactic.BVDecide.LRAT.Internal.CNF
public import Std.Tactic.BVDecide.LRAT.Internal.Actions

@[expose] public section

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open LRAT Result Formula Clause Std Sat

theorem addEmptyCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (rupHints : Array Nat)
    (rupAddSuccess : (Formula.performRupAdd f Clause.empty rupHints).snd = true) :
    Unsatisfiable α f := by
  intro p pf
  let f' := (performRupAdd f empty rupHints).1
  have f'_def : f' = Formula.insert f empty := by grind
  have f_liff_f' : Liff α f (Formula.insert f empty) := by grind
  specialize f_liff_f' p
  rw [f_liff_f', sat_iff_forall] at pf
  have empty_in_f' : empty ∈ toList (Formula.insert f empty) := by grind
  simp only [(· ⊨ ·)] at pf
  grind [Clause.eval]

theorem addRupCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f)
    (f_readyForRatAdd : ReadyForRatAdd f) (c : β) (f' : σ) (rupHints : Array Nat)
    (heq : performRupAdd f c rupHints = (f', true))
    (restPrf : List (Action β α)) (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → WellFormedAction a)
    (ih :
      ReadyForRupAdd f' → ReadyForRatAdd f' → (∀ (a : Action β α), a ∈ restPrf → WellFormedAction a) →
      lratChecker f' restPrf = success → Unsatisfiable α f')
    (f'_success : lratChecker f' restPrf = success) :
    Unsatisfiable α f := by
  grind [Unsatisfiable, Liff]

theorem addRatCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (f_readyForRatAdd : ReadyForRatAdd f) (c : β)
    (pivot : Literal α) (f' : σ) (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat))
    (pivot_limplies_c : Limplies α pivot c) (heq : performRatAdd f c pivot rupHints ratHints = (f', true))
    (restPrf : List (Action β α)) (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → WellFormedAction a)
    (ih :
      ReadyForRupAdd f' → ReadyForRatAdd f' → (∀ (a : Action β α), a ∈ restPrf → WellFormedAction a) →
      lratChecker f' restPrf = success → Unsatisfiable α f')
    (f'_success : lratChecker f' restPrf = success) :
    Unsatisfiable α f := by
  grind [Equisat, limplies_iff_mem]

theorem delCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (f_readyForRatAdd : ReadyForRatAdd f) (ids : Array Nat)
    (restPrf : List (Action β α))
    (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → WellFormedAction a)
    (ih :
      ReadyForRupAdd (delete f ids) → ReadyForRatAdd (delete f ids) → (∀ (a : Action β α), a ∈ restPrf → WellFormedAction a) →
      lratChecker (delete f ids) restPrf = success → Unsatisfiable α (delete f ids))
    (h : lratChecker (Formula.delete f ids) restPrf = success) :
    Unsatisfiable α f := by
  intro p pf
  exact ih (by grind) (by grind) restPrfWellFormed h p (limplies_delete p pf)

theorem lratCheckerSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (f_readyForRatAdd : ReadyForRatAdd f)
    (prf : List (Action β α)) (prfWellFormed : ∀ a : Action β α, a ∈ prf → WellFormedAction a) :
    lratChecker f prf = success → Unsatisfiable α f := by
  induction prf generalizing f
  · unfold lratChecker
    grind
  · simp only [List.mem_cons, forall_eq_or_imp] at prfWellFormed
    unfold lratChecker
    grind [addEmptyCaseSound, addRupCaseSound, addRatCaseSound, delCaseSound, WellFormedAction]

end Internal
end LRAT
end Std.Tactic.BVDecide

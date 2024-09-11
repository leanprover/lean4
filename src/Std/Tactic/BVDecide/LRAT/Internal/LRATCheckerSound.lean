/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
import Std.Tactic.BVDecide.LRAT.Internal.CNF
import Std.Tactic.BVDecide.LRAT.Internal.Actions

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open LRAT Result Formula Clause Std Sat

theorem addEmptyCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (rupHints : Array Nat)
    (rupAddSuccess : (Formula.performRupAdd f Clause.empty rupHints).snd = true) :
    Unsatisfiable α f := by
  let f' := (performRupAdd f empty rupHints).1
  have f'_def := rupAdd_result f empty rupHints f' f_readyForRupAdd
  rw [← rupAddSuccess] at f'_def
  specialize f'_def rfl
  have f_liff_f' := rupAdd_sound f empty rupHints f' f_readyForRupAdd
  rw [← rupAddSuccess] at f_liff_f'
  specialize f_liff_f' rfl
  rw [f'_def] at f_liff_f'
  intro p pf
  specialize f_liff_f' p
  rw [f_liff_f', sat_iff_forall] at pf
  have empty_in_f' : empty ∈ toList (Formula.insert f empty) := by
    rw [Formula.insert_iff]
    exact Or.inl rfl
  specialize pf empty empty_in_f'
  simp [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq, Prod.exists, Bool.exists_bool,
    empty_eq, List.any_nil] at pf

theorem addRupCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f)
    (f_readyForRatAdd : ReadyForRatAdd f) (c : β) (f' : σ) (rupHints : Array Nat)
    (heq : performRupAdd f c rupHints = (f', true))
    (restPrf : List (Action β α)) (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → WellFormedAction a)
    (ih : ∀ (f : σ),
      ReadyForRupAdd f → ReadyForRatAdd f → (∀ (a : Action β α), a ∈ restPrf → WellFormedAction a) →
      lratChecker f restPrf = success → Unsatisfiable α f)
    (f'_success : lratChecker f' restPrf = success) :
    Unsatisfiable α f := by
  have f'_def := rupAdd_result f c rupHints f' f_readyForRupAdd heq
  have f'_readyForRupAdd : ReadyForRupAdd f' := by
    rw [f'_def]
    exact readyForRupAdd_insert f c f_readyForRupAdd
  have f'_readyForRatAdd : ReadyForRatAdd f' := by
    rw [f'_def]
    exact readyForRatAdd_insert f c f_readyForRatAdd
  specialize ih f' f'_readyForRupAdd f'_readyForRatAdd restPrfWellFormed f'_success
  have f_liff_f' : Liff α f f' := rupAdd_sound f c rupHints f' f_readyForRupAdd heq
  intro p pf
  rw [f_liff_f' p] at pf
  exact ih p pf

theorem addRatCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (f_readyForRatAdd : ReadyForRatAdd f) (c : β)
    (pivot : Literal α) (f' : σ) (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat))
    (pivot_limplies_c : Limplies α pivot c) (heq : performRatAdd f c pivot rupHints ratHints = (f', true))
    (restPrf : List (Action β α)) (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → WellFormedAction a)
    (ih : ∀ (f : σ),
      ReadyForRupAdd f → ReadyForRatAdd f → (∀ (a : Action β α), a ∈ restPrf → WellFormedAction a) →
      lratChecker f restPrf = success → Unsatisfiable α f)
    (f'_success : lratChecker f' restPrf = success) :
    Unsatisfiable α f := by
  rw [limplies_iff_mem] at pivot_limplies_c
  have f'_def := ratAdd_result f c pivot rupHints ratHints f' f_readyForRatAdd pivot_limplies_c heq
  have f'_readyForRupAdd : ReadyForRupAdd f' := by
    rw [f'_def]
    exact readyForRupAdd_insert f c f_readyForRupAdd
  have f'_readyForRatAdd : ReadyForRatAdd f' := by
    rw [f'_def]
    exact readyForRatAdd_insert f c f_readyForRatAdd
  specialize ih f' f'_readyForRupAdd f'_readyForRatAdd restPrfWellFormed f'_success
  have f_equisat_f' : Equisat α f f' := ratAdd_sound f c pivot rupHints ratHints f' f_readyForRatAdd pivot_limplies_c heq
  intro p pf
  rw [Equisat] at f_equisat_f'
  rw [← f_equisat_f'] at ih
  exact ih p pf

theorem delCaseSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (f_readyForRatAdd : ReadyForRatAdd f) (ids : Array Nat)
    (restPrf : List (Action β α))
    (restPrfWellFormed : ∀ (a : Action β α), a ∈ restPrf → WellFormedAction a)
    (ih : ∀ (f : σ),
      ReadyForRupAdd f → ReadyForRatAdd f → (∀ (a : Action β α), a ∈ restPrf → WellFormedAction a) →
      lratChecker f restPrf = success → Unsatisfiable α f)
    (h : lratChecker (Formula.delete f ids) restPrf = success) :
    Unsatisfiable α f := by
  intro p pf
  have f_del_readyForRupAdd : ReadyForRupAdd (Formula.delete f ids) := readyForRupAdd_delete f ids f_readyForRupAdd
  have f_del_readyForRatAdd : ReadyForRatAdd (Formula.delete f ids) := readyForRatAdd_delete f ids f_readyForRatAdd
  exact ih (delete f ids) f_del_readyForRupAdd f_del_readyForRatAdd restPrfWellFormed h p (limplies_delete p pf)

theorem lratCheckerSound [DecidableEq α] [Clause α β] [Entails α σ] [Formula α β σ] (f : σ)
    (f_readyForRupAdd : ReadyForRupAdd f) (f_readyForRatAdd : ReadyForRatAdd f)
    (prf : List (Action β α)) (prfWellFormed : ∀ a : Action β α, a ∈ prf → WellFormedAction a) :
    lratChecker f prf = success → Unsatisfiable α f := by
  induction prf generalizing f
  · unfold lratChecker
    simp [false_implies]
  · next action restPrf ih =>
    simp only [List.find?, List.mem_cons, forall_eq_or_imp] at prfWellFormed
    rcases prfWellFormed with ⟨actionWellFormed, restPrfWellFormed⟩
    unfold lratChecker
    split
    · intro h
      exfalso
      simp at h
    · next id rupHints restPrf' _ =>
      simp [ite_eq_left_iff, Bool.not_eq_true]
      intro rupAddSuccess
      exact addEmptyCaseSound f f_readyForRupAdd rupHints rupAddSuccess
    · next id c rupHints restPrf' hprf =>
      split
      next f' checkSuccess heq =>
      split
      · next hCheckSuccess =>
        intro f'_success
        simp only [List.cons.injEq] at hprf
        rw [← hprf.2] at f'_success
        rw [hCheckSuccess] at heq
        exact addRupCaseSound f f_readyForRupAdd f_readyForRatAdd c f' rupHints heq restPrf restPrfWellFormed ih f'_success
      · simp [false_implies]
    · next id c pivot rupHints ratHints restPrf' hprf =>
      split
      next f' checkSuccess heq =>
      split
      · next hCheckSuccess =>
        intro f'_success
        simp only [List.cons.injEq] at hprf
        rw [← hprf.2] at f'_success
        rw [hCheckSuccess] at heq
        simp only [WellFormedAction, hprf.1] at actionWellFormed
        exact addRatCaseSound f f_readyForRupAdd f_readyForRatAdd c pivot f' rupHints ratHints actionWellFormed heq restPrf
          restPrfWellFormed ih f'_success
      · simp [false_implies]
    · next ids restPrf' hprf =>
      intro h
      simp only [List.cons.injEq] at hprf
      rw [← hprf.2] at h
      exact delCaseSound f f_readyForRupAdd f_readyForRatAdd ids restPrf restPrfWellFormed ih h

end Internal
end LRAT
end Std.Tactic.BVDecide

set_option grind.warning false

namespace Std
namespace Sat

abbrev Literal (α : Type u) := α × Bool
abbrev CNF.Clause (α : Type u) : Type u := List (Literal α)

end Sat
end Std

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

class Entails (α : Type u) (β : Type v) where
  eval : (α → Bool) → β → Prop

scoped infix:25 " ⊨ " => Entails.eval
scoped notation:25 a:25 " ⊭ " f:30 => ¬(Entails.eval a f)

def Unsatisfiable (α : Type u) {σ : Type v} [Entails α σ] (f : σ) : Prop :=
  ∀ (a : α → Bool), a ⊭ f

def Limplies (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  ∀ (a : α → Bool), a ⊨ f1 → a ⊨ f2

def Incompatible (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  ∀ (a : α → Bool), (a ⊭ f1) ∨ (a ⊭ f2)

def PosFin (n : Nat) := {x : Nat // 0 < x ∧ x < n}

inductive Assignment

namespace Assignment

def hasAssignment (b : Bool) (a : Assignment) : Bool := sorry

instance {n : Nat} : Entails (PosFin n) (Array Assignment) where
  eval := fun p arr => ∀ i : PosFin n, sorry

end Assignment

open Std.Sat

namespace Clause

instance : Entails α (Literal α) where
  eval := fun p l => p l.1 = l.2

end Clause

structure DefaultClause (numVarsSucc : Nat) where
  clause : CNF.Clause Unit

open Std.Sat
open Assignment DefaultClause

structure DefaultFormula (numVarsSucc : Nat) where
  clauses : Array (Option (DefaultClause numVarsSucc))
  rupUnits : Array Unit
  ratUnits : Array Unit
  assignments : Array Assignment

namespace DefaultFormula

def toList {n : Nat} (f : DefaultFormula n) : List (DefaultClause n) := []

instance {n : Nat} : Entails (PosFin n) (DefaultFormula n) where
  eval := fun p f => (toList f).all sorry

def confirmRupHint {n : Nat} (clauses : Array (Option (DefaultClause n))) :
    Array Assignment × CNF.Clause (PosFin n) × Bool × Bool → Nat →
    Array Assignment × CNF.Clause (PosFin n) × Bool × Bool := sorry

def performRupCheck {n : Nat} (f : DefaultFormula n) (rupHints : Array Nat) :
    DefaultFormula n × CNF.Clause (PosFin n) × Bool × Bool :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  let (assignments, derivedLits, derivedEmpty, encounteredError) := rupHints.foldl (confirmRupHint clauses) (assignments, [], false, false)
  (⟨clauses, rupUnits, ratUnits, assignments⟩, derivedLits, derivedEmpty, encounteredError)

open Assignment

open Std.Sat

def AssignmentsInvariant {n : Nat} (f : DefaultFormula n) : Prop :=
  ∃ hsize : f.assignments.size = n, ∀ i : PosFin n, ∀ b : Bool,
    hasAssignment b (f.assignments[i.1]'(by rw [hsize]; exact i.2.2)) →
    Limplies (PosFin n) f (i, b)

def ConfirmRupHintFoldEntailsMotive {n : Nat} (f : DefaultFormula n) (_idx : Nat)
    (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) :
    Prop :=
  acc.1.size = n ∧ Limplies (PosFin n) f acc.1 ∧ (acc.2.2.1 → Incompatible (PosFin n) acc.1 f)

theorem assignmentsInvariant_performRupCheck_of_assignmentsInvariant {n : Nat} (f : DefaultFormula n)
    (f_AssignmentsInvariant : AssignmentsInvariant f) (rupHints : Array Nat) :
    AssignmentsInvariant (performRupCheck f rupHints).1 := by
  rcases Array.foldl_induction (ConfirmRupHintFoldEntailsMotive f) sorry sorry with ⟨hsize, h1, _⟩
  apply Exists.intro hsize
  intro i b h p pf
  have i_in_bounds :
    i.1 < (rupHints.foldl (fun b => confirmRupHint f.clauses b) (f.assignments, [], false, false) 0 rupHints.size).1.size := by
    let in_bounds_motive (_idx : Nat) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) := acc.1.size = n
    have in_bounds_inductive (idx : Fin rupHints.size) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool)
      (ih : in_bounds_motive idx.1 acc) : in_bounds_motive (idx.1 + 1) (confirmRupHint f.clauses acc rupHints[idx]) := by
      have h : (confirmRupHint f.clauses (acc.fst, acc.snd.fst, acc.snd.snd.fst, acc.snd.snd.snd) rupHints[idx]).fst.size =
        acc.fst.size := sorry
      have : (acc.fst, acc.snd.fst, acc.snd.snd.fst, acc.snd.snd.snd) = acc := rfl
      simp [this] at *
      grind
    sorry
  sorry

-- Reduce prove above
example {n : Nat} (f : DefaultFormula n)
    (f_AssignmentsInvariant : AssignmentsInvariant f) (rupHints : Array Nat) :
    AssignmentsInvariant (performRupCheck f rupHints).1 := by
  rcases Array.foldl_induction (ConfirmRupHintFoldEntailsMotive f) sorry sorry with ⟨hsize, h1, _⟩
  apply Exists.intro hsize
  intro i b h p pf
  have i_in_bounds :
    i.1 < (rupHints.foldl (fun b => confirmRupHint f.clauses b) (f.assignments, [], false, false) 0 rupHints.size).1.size := by
    let in_bounds_motive (_idx : Nat) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool) := acc.1.size = n
    have in_bounds_inductive (idx : Fin rupHints.size) (acc : Array Assignment × CNF.Clause (PosFin n) × Bool × Bool)
      (ih : in_bounds_motive idx.1 acc) : in_bounds_motive (idx.1 + 1) (confirmRupHint f.clauses acc rupHints[idx]) := by
      have h : (confirmRupHint f.clauses (acc.fst, acc.snd.fst, acc.snd.snd.fst, acc.snd.snd.snd) rupHints[idx]).fst.size =
        acc.fst.size := sorry
      grind
    sorry
  sorry

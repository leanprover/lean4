@[simp] def List.count' [DecidableEq α] : List α → α → Nat
  | [], _    => 0
  | a::as, b => if a = b then as.count' b + 1 else as.count' b

inductive StarsAndBars : Nat → Nat → Type where
  | nil  : StarsAndBars 0 0
  | star : StarsAndBars s b → StarsAndBars (s+1) b
  | bar  : StarsAndBars s b → StarsAndBars s (b+1)

namespace StarsAndBars

namespace Ex1

def toList : StarsAndBars s b → { bs : List Bool // bs.count' false = s ∧ bs.count' true = b }
  | nil    => ⟨[], by simp⟩
  | star h => ⟨false :: toList h, by simp [(toList h).2]⟩
  | bar  h => ⟨true :: toList h, by simp [(toList h).2]⟩

theorem toList_star (h : StarsAndBars s b) (h') : toList (star h) = ⟨false :: toList h, h'⟩ := by
  rfl

theorem toList_bar (h : StarsAndBars s b) (h') : toList (bar h) = ⟨true :: toList h, h'⟩ := by
  rfl

end Ex1

/- Same example with explicit proofs -/
namespace Ex2

theorem toList_star_proof (h : bs.count' false = s ∧ bs.count' true = b) : (false :: bs).count' false = s.succ ∧ (false :: bs).count' true = b := by
  simp [*]

theorem toList_bar_proof (h : bs.count' false = s ∧ bs.count' true = b) : (true :: bs).count' false = s ∧ (true :: bs).count' true = b.succ := by
  simp [*]

def toList : StarsAndBars s b → { bs : List Bool // bs.count' false = s ∧ bs.count' true = b }
  | nil    => ⟨[], by simp⟩
  | star h => ⟨false :: toList h, toList_star_proof (toList h).property⟩
  | bar  h => ⟨true :: toList h,  toList_bar_proof (toList h).property⟩

theorem toList_star (h : StarsAndBars s b) : toList (star h) = ⟨false :: toList h, toList_star_proof (toList h).property⟩ := by
  rfl

theorem toList_bar (h : StarsAndBars s b) : toList (bar h) = ⟨true :: toList h, toList_bar_proof (toList h).property⟩ := by
  rfl

end Ex2

end StarsAndBars

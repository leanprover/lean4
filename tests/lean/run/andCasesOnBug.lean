inductive FinInt: Nat → Type :=
  | nil: FinInt 0
  | next: Bool → FinInt n → FinInt (n+1)
deriving DecidableEq

def zero (sz: Nat): FinInt sz :=
  match sz with
  | 0 => .nil
  | sz+1 => .next false (zero sz)

inductive Pair :=
  | mk (sz: Nat) (lhs rhs: FinInt sz)

def makePair?: (n m: (sz: Nat) × FinInt sz) → Option Pair
  | ⟨sz, lhs⟩, ⟨sz', rhs⟩ =>
      if EQ: true /\ sz = sz' then
            have rhs' : FinInt sz := by {
                cases EQ;
                case intro left right =>
                simp [right];
                exact rhs;
            };
            some (Pair.mk sz lhs rhs')
      else none

def usePair: Pair → Bool := fun ⟨sz, lhs, rhs⟩ => lhs = rhs

#eval (makePair? ⟨8, zero 8⟩ ⟨8, zero 8⟩).map usePair

namespace Ex1

mutual
def h (c : Nat) (x : Nat) := match g c x c c with
  | 0 => 1
  | r => r + 2
termination_by 0
decreasing_by all_goals sorry

def g (c : Nat) (t : Nat) (a b : Nat) : Nat := match t with
  | (n+1) => match g c n a b with
    | 0 => 0
    | m => match g c (n - m) a b with
      | 0 => 0
      | m + 1 => g c m a b
  | 0 => f c 0
termination_by 0
decreasing_by all_goals sorry

def f (c : Nat) (x : Nat) := match h c x with
  | 0 => 1
  | r => f c r
termination_by 0
decreasing_by all_goals sorry
end

attribute [simp] g
attribute [simp] h
attribute [simp] f

#check g._eq_1
#check g._eq_2

#check h._eq_1

#check f._eq_1

end Ex1

namespace Ex2

def g (t : Nat) : Nat := match t with
  | (n+1) => match g n with
    | 0 => 0
    | m + 1 => match g (n - m) with
      | 0 => 0
      | m + 1 => g n
  | 0 => 0
decreasing_by all_goals sorry

theorem ex1 : g 0 = 0 := by
  rw [g]

#check g._eq_1
#check g._eq_2

theorem ex2 : g 0 = 0 := by
  unfold g
  simp

#check g._unfold


end Ex2

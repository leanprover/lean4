
def hello : (x : Nat) → (h : x = x) → True := by
  intro x
  --^ goals
  intro
--^ goals
  trivial

def hello2 : (x : Nat) → (h : x = x) → True := by
  intros
--^ goals
  trivial


theorem qqww (x y : Nat) (f : (α → x = y)) (h : y = x) : True := by
  rw [h] at f
   --^ goals
  trivial

theorem qqww2 (x y : Nat) (f : (α → x = y)) (h : y = x) : True := by
  rw [h] at f
       --^ goals
  trivial

theorem adsf : (True ∧ True) := by
  apply And.intro
--^ goals
  trivial
--^ goals
  trivial
--^ goals

theorem comm (x y z : Nat) (h : y = x) : (x + z) = (z + y) := by
  rw [Nat.add_comm, h]
    --^ goals

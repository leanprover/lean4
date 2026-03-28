module
inductive T (a:Type) where
  | constuctor1: T a
  | constuctor2: T a

instance : LE (T a) where
  le := sorry

axiom L: Type
axiom L.pred (l1: L) (t: T α): Prop

axiom L.pred_le (l1: L) (t1 t2: T α):
  t1 ≤ t2 → l1.pred t1 → l1.pred t2
grind_pattern L.pred_le => t1 ≤ t2, l1.pred t1

abbrev T' := T Unit

axiom l (t: T'): L

-- l keeps the same value when t gets bigger
axiom l_le (t1 t2: T'):
  t1 ≤ t2 → l t1 = l t2
grind_pattern l_le => t1 ≤ t2, l t1

-- construction using l and L.pred
abbrev pred (t: T'): Prop :=
  (l t).pred t

example: pred t1 → t1 ≤ t2 → pred t2 := by
  grind

example: t1 ≤ t2 → pred t1 → pred t2 := by
  grind

def is_mono (p: T' → Prop): Prop :=
  ∀ t1 t2,
    p t1 → t1 ≤ t2 → p t2

example: is_mono pred := by
  grind [is_mono]

example: is_mono pred := by
  unfold is_mono
  grind

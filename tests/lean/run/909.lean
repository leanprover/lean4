structure Date where
  val : Nat
deriving Repr

instance : LE Date := ⟨InvImage (Nat.le) Date.val⟩

instance bad (a b : Date) : Decidable (a <= b) :=
  if h0 : (a.val <= b.val) then isTrue h0 else isFalse (fun hf => False.elim (h0 hf))

instance : Min Date := minOfLe

/-
This implementation also fails:
instance (a b : Date) : Decidable (a <= b) :=
  inferInstanceAs (Decidable (a.val <= b.val))
-/

/-
This implementation evaluates successfully:
instance (a b : Date) : Decidable (a <= b) :=
  dite (a.val <= b.val) isTrue (fun nle => isFalse (fun hf => False.elim (nle hf)))
-/

instance : ToString Date where
  toString d := s!"D{d.val}"

structure DateRange where
  start_ : Date
  finish_ : Date
  h : start_ <= finish_

def r1 := (DateRange.mk (Date.mk 0) (Date.mk 10) (by decide))
-- If you change the start_ value here to `0`, it works.
def r2 := (DateRange.mk (Date.mk 1) (Date.mk 10) (by decide))

#eval min r1.start_ r2.start_

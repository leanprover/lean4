def dividend := 2^65
def divisor := 2^33+1

def correctQuot := 2^32-1
def correctRem := 2^32+1
def wrongRem := 1

theorem correct₁ : dividend / divisor = correctQuot := rfl
theorem correct₂ : dividend = divisor * correctQuot + correctRem := rfl

theorem wrong : dividend % divisor = wrongRem := rfl

theorem unsound : False := by
  have : wrongRem = correctRem := by
    have h := Nat.div_add_mod dividend divisor
    rw [wrong, correct₁, correct₂] at h
    apply Nat.add_left_cancel h
  contradiction

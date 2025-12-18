variable (t1 t2 t3 t4 : Nat)
variable (pf12 : t1 = t2) (pf23 : t2 = t3) (pf34 : t3 = t4)
include pf12 pf23 pf34

theorem foo : t1 = t4 :=
  calc
    t1 = t2 := pf12
    _  = t3 := pf23
    _  = t4 := pf34

variable (t5 : Nat)
variable (pf23' : t2 < t3) (pf45' : t4 < t5)
include pf23' pf45'

instance [LT α] : Trans (α := α) (· < ·) (· < ·) (· < ·) where
  trans := sorry

theorem foo₁ : t1 < t5 :=
  let p := calc
    t1 = t2 := pf12
    _  < t3 := pf23'
    _  = t4 := pf34
    _  < t5 := pf45'
  -- dedent terminates the block
  p

-- same-line `calc <first relation>` with normal indent afterwards
theorem foo₂ : t1 < t5 :=
  calc t1 = t2 := pf12
    _  < t3 := pf23'
    _  = t4 := pf34
    _  < t5 := pf45'

-- `calc <first relation LHS>\n<indent><relation and relation RHS>`
theorem foo₃ : t1 < t5 :=
  calc t1
      = t2 := pf12
    _ < t3 := pf23'
    _ = t4 := pf34
    _ < t5 := pf45'

-- `calc <first relation LHS>\n<indent><relation and relation RHS>`
theorem foo₄ : t1 < t5 :=
  calc t1 = t2 := pf12
       _  < t3 := pf23'
       _  = t4 := pf34
       _  < t5 := pf45'

-- `by` with indented sequence of tactics in `calc`-item RHS
theorem foo₅ : t1 = t4 :=
  calc
    t1 = t2 := pf12
    _  = t3 := by
      skip
      skip
      exact pf23
    _  = t4 := pf34

-- function application with indented argument in `calc`-item RHS
theorem foo₆ : t1 = t4 :=
  calc
    t1 = t2 := pf12
    _  = t3 := id
      pf23
    _  = t4 := pf34

-- `calc <first relation LHS>\n<indent>_ <rel> <rhs> := <proof>` (term)
theorem foo₇ : t1 < t5 :=
  calc t1
    _ = t2 := pf12
    _ < t3 := pf23'
    _ = t4 := pf34
    _ < t5 := pf45'

-- `calc <first relation LHS>\n<indent>_ <rel> <rhs> := <proof>` (tactic)
theorem foo₈ : t1 < t5 := by
  calc t1
    _ = t2 := pf12
    _ < t3 := pf23'
    _ = t4 := pf34
    _ < t5 := pf45'

module

public import Accepted

/-! Several approved hypotheses, nesting, repetition, and a quantified target. -/

public section

theorem task (_ : And Accepted.second (And Accepted.first Accepted.second)) : True := True.intro
theorem plain : True := True.intro
theorem quantified (_ : Accepted.first) (n : Nat) : n = n := rfl
theorem supplied (h : Accepted.first) : Accepted.first := h

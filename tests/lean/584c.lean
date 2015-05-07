section
  parameter (A : Type)

  section
    parameters (a b : A)
    parameter  (H : a = b)

    definition tst₁ := a

    parameter {A}

    definition tst₂ := a

    lemma symm₂ : b = a := eq.symm H

    parameters {a b}
    lemma foo (c : A) (h₂ : c = b) : c = a :=
    eq.trans h₂ symm₂
  end

  parameter (a : A)
  definition tst₃ := a
end

check @tst₁
check @tst₂ -- A is implicit
check @symm₂
check @tst₃  -- A is explicit again
check @foo

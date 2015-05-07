section
  variable (A : Type)

  section
    variables (a b : A)
    variable  (H : a = b)

    definition tst₁ := a

    check @tst₁

    variable {A}

    definition tst₂ := a

    check @tst₂ -- A is implicit

    lemma symm₂ : b = a := eq.symm H

    check @symm₂
  end

  variable (a : A)
  definition tst₃ := a

  check @tst₃  -- A is explicit again
end

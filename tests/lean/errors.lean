namespace foo

definition tst1 : nat → nat → nat :=
a + b  -- ERROR

check tst1

definition tst2 : nat → nat → nat :=
begin
  intro a,
  intro b,
  cases add wth (a, b), -- ERROR
  exact a,
  exact b,
end

  section
    parameter A : Type
    definition tst3 : A → A → A :=
    begin
      intro a,
      apply b, -- ERROR
      exact a
    end

    check tst3
  end

end foo

open nat

noncomputable definition bla : nat :=
foo.tst1 0 0 + foo.tst2 0 0 + foo.tst3 nat 1 1

check foo.tst1
check foo.tst2
check foo.tst3

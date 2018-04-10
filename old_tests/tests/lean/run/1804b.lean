namespace bla

private def foo (x : nat) : nat :=
match x with
| 0 := 1
| _ := 2
end

example (a : nat) (h : a = foo 0) : a = 1 :=
begin
  simp [foo] at h,
  guard_hyp h := a = 1,
  exact h
end

example (a b : nat) (p : b = 0) (h : a = foo b) : a = 1 :=
begin
  simp [foo] at h,
  simp [p] at h,
  simp [foo._match_1] at h,
  guard_hyp h := a = 1,
  exact h
end

example (a b : nat) (p : b = 0) (h : a = foo b) : a = 1 :=
begin
  simp [foo] at h,
  simp [p] at h,
  simp [foo] at h,
  guard_hyp h := a = 1,
  exact h
end

example (a b : nat) (p : b = 0) (h : a = foo b) : a = 1 :=
begin
  simp [foo, p] at h,
  guard_hyp h := a = 1,
  exact h
end

end bla

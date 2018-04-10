def f {α : Type} (a : α) : α :=
a

example (a : nat) (h : a = 3) : [1,2].map nat.succ = [2, f a] :=
begin
  simp!,
  guard_target nat.succ 2 = f a,
  simp [f, h]
end

def foo : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _  _  := ff

example : foo tt tt = f tt :=
begin
  simp!,
  guard_target tt = f tt,
  simp [f]
end

example (b : bool) (h : b = tt) : foo b tt = f tt :=
begin
  fail_if_success { simp! },
  simp! [h],
  guard_target tt = f tt,
  simp [f]
end

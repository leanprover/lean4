meta def f : nat → nat
| n := f (n + 1)

#eval try_for 100 (f 10)

#eval try_for 1000 (f 10)

meta def mk : nat → list nat
| 0     := []
| (n+1) := n :: mk n

example : true :=
begin
  tactic.fail_if_success (guard(to_bool (try_for 1 ((mk 1000)^.length) = some 1000))),
  constructor
end

example : true :=
begin
  guard (try_for 100 ((mk 1000)^.length) = some 1000),
  constructor
end

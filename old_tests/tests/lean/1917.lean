def foo : ℕ → false
| x :=
match x with
  y := let z := y in foo z /- should fail -/
end

meta def foo2 : ℕ → false
| x :=
match x with
  y := let z := y in foo2 z /- should work -/
end

def boo : ℕ → ℕ → bool
| 0       m := ff
| (n + 1) m :=
  match m with
  o := let z := n in boo n (m+1)
  end

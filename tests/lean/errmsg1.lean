eval fun x, x
print fun x, x

check fun x, x
theorem T (A : Type) (x : A) : Pi (y : A), A
:= _.

theorem T (x : _) : x = x := refl x.

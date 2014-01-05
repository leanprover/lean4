Eval fun x, x
print fun x, x

Check fun x, x
Theorem T (A : Type) (x : A) : Pi (y : A), A
:= _.

Theorem T (x : _) : x = x := Refl x.

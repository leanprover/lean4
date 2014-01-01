Import Real.

Variable exp : Real → Real.
Variable log : Real → Real.
Variable pi  : Real.
Alias π : pi.

Variable sin : Real → Real.
Definition cos x := sin (x - π / 2).
Definition tan x := sin x / cos x.
Definition cot x := cos x / sin x.
Definition sec x := 1 / cos x.
Definition csc x := 1 / sin x.
Definition sinh x := (1 - exp (-2 * x)) / (2 * exp (- x)).
Definition cosh x := (1 + exp (-2 * x)) / (2 * exp (- x)).
Definition tanh x := sinh x / cosh x.
Definition coth x := cosh x / sinh x.
Definition sech x := 1 / cosh x.
Definition csch x := 1 / sinh x.

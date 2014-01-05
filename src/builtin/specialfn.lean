import Real.

variable exp : Real → Real.
variable log : Real → Real.
variable pi  : Real.
alias π : pi.

variable sin : Real → Real.
definition cos x := sin (x - π / 2).
definition tan x := sin x / cos x.
definition cot x := cos x / sin x.
definition sec x := 1 / cos x.
definition csc x := 1 / sin x.
definition sinh x := (1 - exp (-2 * x)) / (2 * exp (- x)).
definition cosh x := (1 + exp (-2 * x)) / (2 * exp (- x)).
definition tanh x := sinh x / cosh x.
definition coth x := cosh x / sinh x.
definition sech x := 1 / cosh x.
definition csch x := 1 / sinh x.

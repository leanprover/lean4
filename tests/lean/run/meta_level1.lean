import system.io
open io

#eval do pp (level.max (level.succ level.zero) (level.param `foo)), put_str "\n"

#eval level.normalize (level.succ (level.max (level.max level.zero (level.succ level.zero)) (level.param `l₁)))

#eval level.imax (level.mvar `m) (level.of_nat 10)

#eval if level.zero = level.zero then "eq" else "neq"

#eval level.occurs (level.param `l2) (level.max (level.param `l1) (level.param `l2))

#eval level.occurs (level.param `l3) (level.max (level.param `l1) (level.param `l2))

#eval level.eqv (level.max (level.param `l1) (level.param `l2)) (level.max (level.param `l2) (level.param `l1))

#eval level.eqv (level.max (level.param `l1) (level.param `l2)) (level.max (level.param `l2) (level.param `l2))

#eval level.has_param (level.max (level.param `l1) (level.param `l2)) `l1
#eval level.has_param (level.max (level.param `l1) (level.param `l2)) `l2
#eval level.has_param (level.max (level.param `l1) (level.param `l2)) `l3

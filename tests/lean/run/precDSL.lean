syntax:max "fn " ident "=>" term : term
syntax:(lead+1) "function " ident "=>" term : term

macro_rules
  | `(fn $x:ident => $b) => `(fun $x:ident => $b)
  | `(function $x:ident => $b) => `(fun $x:ident => $b)

#check id fn x => x + 1
#check id function x => x + 1

macro "addPrec" : prec => `(prec| 65)
macro "mulPrec" : prec => `(prec| 70)

infix:addPrec " +' " => Nat.add
infix:mulPrec " *' " => Nat.mul

#eval 10 +' 2 *' 3

theorem ex1 : 10 +' 2 *' 3 = 16 :=
  rfl

theorem ex2 : 10 + 2 * 3 = 16 :=
  rfl

infix:(addPrec-1) " *'' " => Nat.mul

theorem ex3 : 10 +' 2 *'' 3 = 36 :=
  rfl

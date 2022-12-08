structure Minus where
  «i-love-lisp» : Bool

#check Minus.«i-love-lisp»
#check { «i-love-lisp» := true : Minus }
#check fun (x : Minus) => x.«i-love-lisp»
#check fun (x : Minus) => (x).«i-love-lisp»

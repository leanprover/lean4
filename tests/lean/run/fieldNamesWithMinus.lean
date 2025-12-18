structure Minus where
  «i-love-lisp» : Bool

/-- info: Minus.«i-love-lisp» (self : Minus) : Bool -/
#guard_msgs in
#check Minus.«i-love-lisp»

/-- info: { «i-love-lisp» := true } : Minus -/
#guard_msgs in
#check { «i-love-lisp» := true : Minus }

/-- info: fun x => x.«i-love-lisp» : Minus → Bool -/
#guard_msgs in
#check fun (x : Minus) => x.«i-love-lisp»

/-- info: fun x => x.«i-love-lisp» : Minus → Bool -/
#guard_msgs in
#check fun (x : Minus) => (x).«i-love-lisp»

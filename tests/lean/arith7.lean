Import Int.
Eval | -2 |
(*
   Unfortunately, we can't write |-2|, because |- is considered a single token.
   It is not wise to change that since the symbol |- can be used as the notation for
   entailment relation in Lean.
*)
Eval |3|
Definition x : Int := -3
Eval |x + 1|
Eval |x + 1| > 0
Variable y : Int
Eval |x + y|
Show |x + y| > x
SetOption pp::notation false
Show |x + y| > x
Show |x + y| + |y + x| > x
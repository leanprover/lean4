#eval (1,(2,3)).2.fst

#check 31.

#check 31.e

#check 31.ee

#check 31.f

#check 31.ff

#check 11.toDigits 13

#check (11).toDigits 13

#eval (11).toDigits 13

-- This example (adapted from structInst4.lean) exercises the difference betwee
-- term parsing and LVal parsing; the latter fails if we allow `2.snd` to parse
-- as a scientificLit followed by an error token, so this test captures
-- that we have to throw the error token right away, positioned before, rather
-- than after the `2.`
structure Foo where
  (x : Nat × (Nat × Nat) := (2, (4, 5)))
def foo : Foo := {}
#check foo.x.2.snd
#eval { foo with x.2.snd := 1 }

#eval (1,(2,3)).2.fst

#check 31.
#check 31.0
#eval 31.
#eval 31.0

#check 31.e
#check 31.ee

#check 31.f
#check 31.ff

#check 31.3e
#check 31.3e2
#check 31.3ee2

#check 31.3f
#check 31.3f2
#check 31.3ff2

#check 11.toDigits 13
#check (11).toDigits 13
#eval  (11).toDigits 13
#check (11).toDigits(13)
#check (11).toDigits (13)

def succ (a: Nat) := a + 1
def foo {A B} (_: A) (_: B) : Unit := ()
#check foo 31.succ
#check foo (31).succ
#check foo 31(.succ)
#check foo (31)(.succ)
#check foo 31 .succ
#check foo 31. succ

#check 11succ
#check 11.succ
#check 11.12succ
#check (11.succ)
#check (11.12succ)


-- This example (adapted from structInst4.lean) exercises the difference betwee
-- term parsing and LVal parsing; the latter fails if we allow `2.snd` to parse
-- as a scientificLit followed by an error token, so this test captures
-- that we have to throw the error token right away, positioned before, rather
-- than after the `2.`
structure Foo where
  (x : Nat × (Nat × Nat) := (2, (4, 5)))
def bar : Foo := {}
#check bar.x.2.snd
#eval { bar with x.2.snd := 1 }

inductive Nope where
  | succ : Nope -> Nope -> Nope
  | leaf : Nope

example := (match · with
  | succ x y => 4)

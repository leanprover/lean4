import Lean

/-!
`deriving Repr` on a mutual block generates one block of auxiliary functions for the whole block
instead of one per type, and still names each instance after its own type.
-/

mutual
inductive A where
  | a (b : B)
  | leaf
  deriving Repr
inductive B where
  | b (a : A)
  | leaf
  deriving Repr
end

/-- info: A.a (B.b (A.leaf)) -/
#guard_msgs in #eval A.a (.b .leaf)

/-- info: B.b (A.a (B.leaf)) -/
#guard_msgs in #eval B.b (.a .leaf)

example : Repr A := instReprA
example : Repr B := instReprB

open Lean in
run_meta do
  let env ← getEnv
  for n in [`instReprA.repr_1, `instReprA.repr_2] do
    unless env.contains n do throwError "missing {n}"
  for n in [`instReprB.repr_1, `instReprB.repr_2] do
    if env.contains n then throwError "unexpected duplicate aux function {n}"

/-! Types from different mutual blocks in one `deriving instance` command. -/

mutual
inductive C where
  | c (d : D)
  | leaf
inductive D where
  | d (c : C)
  | leaf
end

inductive E where
  | e (n : Nat)

deriving instance Repr for C, E, D

/-- info: C.c (D.d (C.leaf)) -/
#guard_msgs in #eval C.c (.d .leaf)

/-- info: D.d (C.c (D.leaf)) -/
#guard_msgs in #eval D.d (.c .leaf)

/-- info: E.e 3 -/
#guard_msgs in #eval E.e 3

example : Repr C := instReprC
example : Repr D := instReprD
example : Repr E := instReprE

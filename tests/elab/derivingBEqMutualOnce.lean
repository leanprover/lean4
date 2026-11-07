import Lean

/-!
`deriving BEq` on a mutual block generates one block of auxiliary functions for the whole block
instead of one per type, and still names each instance after its own type.
-/

mutual
inductive A where
  | a (b : B)
  | leaf
  deriving BEq
inductive B where
  | b (a : A)
  | leaf
  deriving BEq
end

#guard A.a (.b .leaf) == A.a (.b .leaf)
#guard A.a (.b .leaf) != A.a .leaf
#guard B.b (.a .leaf) == B.b (.a .leaf)
#guard B.b (.a .leaf) != B.leaf

example : BEq A := instBEqA
example : BEq B := instBEqB

open Lean in
run_meta do
  let env ← getEnv
  for n in [`instBEqA.beq_1, `instBEqA.beq_2] do
    unless env.contains n do throwError "missing {n}"
  for n in [`instBEqB.beq_1, `instBEqB.beq_2] do
    if env.contains n then throwError "unexpected duplicate aux function {n}"

/-! Types from different mutual blocks, and an enum, in one `deriving instance` command. -/

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

inductive F where
  | x | y

deriving instance BEq for C, E, F, D

#guard C.c (.d .leaf) == C.c (.d .leaf)
#guard C.c (.d .leaf) != C.leaf
#guard D.d (.c .leaf) == D.d (.c .leaf)
#guard E.e 3 == E.e 3
#guard E.e 3 != E.e 4
#guard F.x == F.x
#guard F.x != F.y

example : BEq C := instBEqC
example : BEq D := instBEqD
example : BEq E := instBEqE
example : BEq F := instBEqF

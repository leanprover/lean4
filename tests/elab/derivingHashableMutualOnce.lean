import Lean

/-!
`deriving Hashable` on a mutual block generates one block of auxiliary functions for the whole
block instead of one per type, and still names each instance after its own type.
-/

mutual
inductive A where
  | a (b : B)
  | leaf
  deriving Hashable
inductive B where
  | b (a : A)
  | leaf
  deriving Hashable
end

#guard hash (A.a (.b .leaf)) == hash (A.a (.b .leaf))
#guard hash (A.a (.b .leaf)) != hash (A.a .leaf)
#guard hash (B.b (.a .leaf)) != hash B.leaf

example : Hashable A := instHashableA
example : Hashable B := instHashableB

open Lean in
run_meta do
  let env ← getEnv
  for n in [`instHashableA.hash_1, `instHashableA.hash_2] do
    unless env.contains n do throwError "missing {n}"
  for n in [`instHashableB.hash_1, `instHashableB.hash_2] do
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

deriving instance Hashable for C, E, D

#guard hash (C.c (.d .leaf)) == hash (C.c (.d .leaf))
#guard hash (D.d (.c .leaf)) != hash D.leaf
#guard hash (E.e 3) != hash (E.e 4)

example : Hashable C := instHashableC
example : Hashable D := instHashableD
example : Hashable E := instHashableE

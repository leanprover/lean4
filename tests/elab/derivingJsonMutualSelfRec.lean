import Lean.Data.Json
open Lean

/-!
`deriving ToJson`/`FromJson` for a `mutual` group used to dispatch a *self*
recursive constructor argument to the group's *first* auxiliary function rather
than the one being generated, producing ill-typed code:

    Application type mismatch: The argument a✝
      has type              B
      but is expected to have type  A
    in the application    toJson_1 a✝

Only a member other than the first was affected, since the first member's own
auxiliary function is the one that was used.
-/


mutual
inductive A where
  | a1 : Nat → A
  | a2 : B → A
inductive B where
  | b1 : Nat → B
  | b2 : B → B          -- self-recursive, in a non-first member
end

deriving instance ToJson for A, B
deriving instance FromJson for A, B

/-- info: {"a2": {"b2": {"b1": 7}}} -/
#guard_msgs in
#eval toJson (A.a2 (.b2 (.b1 7)))

/-- info: true -/
#guard_msgs in
#eval ((fromJson? (toJson (A.a2 (.b2 (.b1 7)))) : Except String A)).toOption.isSome

-- self-recursion three members deep, and in the last member
mutual
inductive C where
  | c1 : D → C
inductive D where
  | d1 : E → D
inductive E where
  | e1 : Nat → E
  | e2 : E → E
end

deriving instance ToJson for C, D, E
deriving instance FromJson for C, D, E

/-- info: {"c1": {"d1": {"e2": {"e1": 1}}}} -/
#guard_msgs in
#eval toJson (C.c1 (.d1 (.e2 (.e1 1))))

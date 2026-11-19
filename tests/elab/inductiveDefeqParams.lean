/-! The parameter types of the datatypes in a mutual inductive declaration only have to agree up to
definitional equality; the kernel compares them with `isDefEq` (`check_inductive_types`), as it does
for the leading binders of each constructor (`check_constructors`). Nothing normalizes them, so the
declared type formers keep the parameter types as written. -/

mutual
inductive Id1 (a : Type) : Type where
  | mk : Id2 a → Id1 a

inductive Id2 (a : id Type) : Type where
  | mk : Id1 a → Id2 a
end

/--
info: inductive Id1 : Type → Type
number of parameters: 1
constructors:
Id1.mk : {a : Type} → Id2 a → Id1 a
-/
#guard_msgs in
#print Id1

/--
info: inductive Id2 : id Type → Type
number of parameters: 1
constructors:
Id2.mk : {a : Type} → Id1 a → Id2 a
-/
#guard_msgs in
#print Id2

-- The constructors of both datatypes take the parameter type of the *first* type former, so it is
-- that one the kernel compares each constructor telescope against.
mutual
inductive J1 (a : id Type) : Type where
  | mk : J2 a → J1 a

inductive J2 (a : Type) : Type where
  | mk : J1 a → J2 a
end

/-- info: constructor J2.mk : {a : id Type} → J1 a → J2 a -/
#guard_msgs in
#print J2.mk

inductive K (a : id Type) : Type where
  | mk : K a → K a

/-- info: constructor K.mk : {a : id Type} → K a → K a -/
#guard_msgs in
#print K.mk

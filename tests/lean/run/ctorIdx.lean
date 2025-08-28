inductive Enum where | a1 | a2 | a3 | a4 | a5
deriving DecidableEq

/--
info: @[reducible] protected def Enum.ctorIdx : Enum → Nat :=
fun x => Enum.casesOn x 0 1 2 3 4
-/
#guard_msgs in
#print Enum.ctorIdx

inductive NonRec where | a1 (u : Unit) | a2 (i : Int) | a3 (n : Nat) (f : Fin n) | a4 (s : String) (b : Bool) | a5

/--
info: @[reducible] protected def NonRec.ctorIdx : NonRec → Nat :=
fun x => NonRec.casesOn x (fun u => 0) (fun i => 1) (fun n f => 2) (fun s b => 3) 4
-/
#guard_msgs in
#print NonRec.ctorIdx


inductive Nested (α : Type) where
  | a1 (x : α)
  | a2 (y : Nested α)
  | a3 (z : List (Nested α))

/--
info: @[reducible] protected def Nested.ctorIdx : {α : Type} → Nested α → Nat :=
fun {α} x => x.casesOn (fun x => 0) (fun y => 1) fun z => 2
-/
#guard_msgs in
#print Nested.ctorIdx

mutual
inductive A (m : Nat) : Nat → Type
  | self : A m n → A m (n+m)
  | other : B m n → A m (n+m)
  | empty : A m 0
inductive B (m : Nat) : Nat → Type
  | self : B m n → B m (n+m)
  | other : A m n → B m (n+m)
  | empty : B m 0
end

/--
info: @[reducible] protected def A.ctorIdx : {m a : Nat} → A m a → Nat :=
fun {m a} x => x.casesOn (fun {n} a => 0) (fun {n} a => 1) 2
-/
#guard_msgs in
#print A.ctorIdx
/--
info: @[reducible] protected def B.ctorIdx : {m a : Nat} → B m a → Nat :=
fun {m a} x => x.casesOn (fun {n} a => 0) (fun {n} a => 1) 2
-/
#guard_msgs in
#print B.ctorIdx

-- Single constructor inductives do not use casesOn

inductive Single where | only (n : Nat)
/--
info: @[reducible] protected def Single.ctorIdx : Single → Nat :=
fun x => 0
-/
#guard_msgs in #print Single.ctorIdx

structure Struct where
  field1 : Nat
  field2 : Bool
/--
info: @[reducible] protected def Struct.ctorIdx : Struct → Nat :=
fun x => 0
-/
#guard_msgs in #print Struct.ctorIdx

-- Unsafe inductives do get a definition

unsafe inductive U : Type | mk : (U → U) → U
/--
info: @[reducible] unsafe protected def U.ctorIdx : U → Nat :=
fun x => 0
-/
#guard_msgs in
#print U.ctorIdx

-- This should not get a ctorIdx, only types should

inductive Eq' : α → α → Prop where | refl (a : α) : Eq' a a
/-- error: Unknown constant `Eq'.ctorIdx` -/
#guard_msgs in
#print Eq'.ctorIdx


set_option linter.deprecated true

-- Enumeration types get a deprecated alias, other types dont
/-- info: Enum.toCtorIdx : Enum → Nat -/
#guard_msgs in #check Enum.toCtorIdx
/-- warning: `Enum.toCtorIdx` has been deprecated: Use `Enum.ctorIdx` instead -/
#guard_msgs in example := Enum.toCtorIdx
/-- error: Unknown identifier `Nonrec.toCtorIdx` -/
#guard_msgs in #check Nonrec.toCtorIdx

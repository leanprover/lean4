/-!
  Test #print command for structures and classes
-/

/- Structure -/
/--
info: structure Prod.{u, v} : Type u → Type v → Type (max u v)
number of parameters: 2
constructor:
Prod.mk : {α : Type u} → {β : Type v} → α → β → α × β
fields:
fst : α
snd : β
-/
#guard_msgs in
#print Prod

/- Class -/
/--
info: class Inhabited.{u} : Sort u → Sort (max 1 u)
number of parameters: 1
constructor:
Inhabited.mk : {α : Sort u} → α → Inhabited α
fields:
default : α
-/
#guard_msgs in
#print Inhabited

/- Structure with private field -/
/--
info: structure Thunk.{u} : Type u → Type u
number of parameters: 1
constructor:
Thunk.mk : {α : Type u} → (Unit → α) → Thunk α
fields:
private fn : Unit → α
-/
#guard_msgs in
#print Thunk

/- Extended class -/
/--
info: class Alternative.{u, v} : (Type u → Type v) → Type (max (u + 1) v)
number of parameters: 1
constructor:
Alternative.mk : {f : Type u → Type v} →
  [toApplicative : Applicative f] → ({α : Type u} → f α) → ({α : Type u} → f α → (Unit → f α) → f α) → Alternative f
fields:
toApplicative : Applicative f
failure : {α : Type u} → f α
orElse : {α : Type u} → f α → (Unit → f α) → f α
-/
#guard_msgs in
#print Alternative

/- Multiply extended class -/
/--
info: class Applicative.{u, v} : (Type u → Type v) → Type (max (u + 1) v)
number of parameters: 1
constructor:
Applicative.mk : {f : Type u → Type v} →
  [toFunctor : Functor f] →
    [toPure : Pure f] → [toSeq : Seq f] → [toSeqLeft : SeqLeft f] → [toSeqRight : SeqRight f] → Applicative f
fields:
toFunctor : Functor f
toPure : Pure f
toSeq : Seq f
toSeqLeft : SeqLeft f
toSeqRight : SeqRight f
-/
#guard_msgs in
#print Applicative

/- Structure with unused parameter -/

structure Weird (α β : Type _) where
  a : α

/--
info: structure Weird.{u_1, u_2} : Type u_1 → Type u_2 → Type u_1
number of parameters: 2
constructor:
Weird.mk : {α : Type u_1} → {β : Type u_2} → α → Weird α β
fields:
a : α
-/
#guard_msgs in
#print Weird

/- Structure-like inductive -/

inductive Fake (α : Type _) where
  | mk : (x : α) → Fake α

/--
info: inductive Fake.{u_1} : Type u_1 → Type u_1
number of parameters: 1
constructors:
Fake.mk : {α : Type u_1} → α → Fake α
-/
#guard_msgs in
#print Fake

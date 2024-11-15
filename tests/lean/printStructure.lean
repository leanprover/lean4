/-!
  Test #print command for structures and classes
-/

/- Structure -/
/--
info: structure Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
number of parameters: 2
fields:
  Prod.fst : α
  Prod.snd : β
constructor:
  Prod.mk : {α : Type u} → {β : Type v} → α → β → α × β
-/
#guard_msgs in
#print Prod

/- Class -/
/--
info: class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
number of parameters: 1
fields:
  Inhabited.default : α
constructor:
  Inhabited.mk : {α : Sort u} → α → Inhabited α
-/
#guard_msgs in
#print Inhabited

/- Structure with private field -/
/--
info: structure Thunk.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  private _root_.Thunk.fn : Unit → α
constructor:
  Thunk.mk : {α : Type u} → (Unit → α) → Thunk α
-/
#guard_msgs in
#print Thunk

/- Extended class -/
/--
info: class Alternative.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
parents:
  Alternative.toApplicative : Applicative f
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β
  Functor.mapConst : {α β : Type u} → α → f β → f α
  Pure.pure : {α : Type u} → α → f α
  Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
  SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β
  Alternative.failure : {α : Type u} → f α
  Alternative.orElse : {α : Type u} → f α → (Unit → f α) → f α
constructor:
  Alternative.mk : {f : Type u → Type v} →
    [toApplicative : Applicative f] → ({α : Type u} → f α) → ({α : Type u} → f α → (Unit → f α) → f α) → Alternative f
resolution order:
  Alternative, Applicative, Functor, Pure, Seq, SeqLeft, SeqRight
-/
#guard_msgs in
#print Alternative

/- Multiply extended class -/
/--
info: class Applicative.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
parents:
  Applicative.toFunctor : Functor f
  Applicative.toPure : Pure f
  Applicative.toSeq : Seq f
  Applicative.toSeqLeft : SeqLeft f
  Applicative.toSeqRight : SeqRight f
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β
  Functor.mapConst : {α β : Type u} → α → f β → f α
  Pure.pure : {α : Type u} → α → f α
  Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
  SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β
constructor:
  Applicative.mk : {f : Type u → Type v} →
    [toFunctor : Functor f] →
      [toPure : Pure f] → [toSeq : Seq f] → [toSeqLeft : SeqLeft f] → [toSeqRight : SeqRight f] → Applicative f
resolution order:
  Applicative, Functor, Pure, Seq, SeqLeft, SeqRight
-/
#guard_msgs in
#print Applicative

/- Structure with unused parameter -/

structure Weird (α β : Type _) where
  a : α

/--
info: structure Weird.{u_1, u_2} (α : Type u_1) (β : Type u_2) : Type u_1
number of parameters: 2
fields:
  Weird.a : α
constructor:
  Weird.mk : {α : Type u_1} → {β : Type u_2} → α → Weird α β
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

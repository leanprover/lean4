/-!
# Test `#print` command for structures and classes
-/

/-! Structure -/
/--
info: structure Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
number of parameters: 2
fields:
  Prod.fst : α
  Prod.snd : β
constructor:
  Prod.mk.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) : α × β
-/
#guard_msgs in
#print Prod

/-! Class -/
/--
info: class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
number of parameters: 1
fields:
  Inhabited.default : α
constructor:
  Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α
-/
#guard_msgs in
#print Inhabited

/-! Structure with private field, imported -/
/--
info: structure Thunk.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  private Thunk.fn✝ : Unit → α
constructor:
  Thunk.mk.{u} {α : Type u} (fn : Unit → α) : Thunk α
-/
#guard_msgs in
#print Thunk

/-! Structure with private field, current module -/
structure PrivField where
  private x : Nat

/--
info: structure PrivField : Type
number of parameters: 0
fields:
  private PrivField.x : Nat
constructor:
  PrivField.mk (x : Nat) : PrivField
-/
#guard_msgs in
#print PrivField

/-! Private constructor, imported -/
/--
info: class TypeName.{u} (α : Type u) : Type
number of parameters: 1
fields:
  private TypeName.data✝ : (TypeNameData✝ α).type
constructor:
  private TypeName.mk'✝.{u} {α : Type u} (data : (TypeNameData✝ α).type) : TypeName α
-/
#guard_msgs in
#print TypeName

/-! Private constructor, current module -/
structure PrivCtor where private mk ::
  x : Nat
/--
info: structure PrivCtor : Type
number of parameters: 0
fields:
  PrivCtor.x : Nat
constructor:
  private PrivCtor.mk (x : Nat) : PrivCtor
-/
#guard_msgs in
#print PrivCtor

/-! Extended class -/
/--
info: class Alternative.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
parents:
  Alternative.toApplicative : Applicative f
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β :=
    fun {α β} x y => pure x <*> y
  Functor.mapConst : {α β : Type u} → α → f β → f α :=
    fun {α β} => Functor.map ∘ Function.const β
  Pure.pure : {α : Type u} → α → f α
  Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α :=
    fun {α β} a b => Function.const β <$> a <*> b ()
  SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β :=
    fun {α β} a b => Function.const α id <$> a <*> b ()
  Alternative.failure : {α : Type u} → f α
  Alternative.orElse : {α : Type u} → f α → (Unit → f α) → f α
constructor:
  Alternative.mk.{u, v} {f : Type u → Type v} [toApplicative : Applicative f] (failure : {α : Type u} → f α)
    (orElse : {α : Type u} → f α → (Unit → f α) → f α) : Alternative f
field notation resolution order:
  Alternative, Applicative, Functor, Pure, Seq, SeqLeft, SeqRight
-/
#guard_msgs in
#print Alternative

/-! Multiply extended class -/
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
  Functor.map : {α β : Type u} → (α → β) → f α → f β :=
    fun {α β} x y => pure x <*> y
  Functor.mapConst : {α β : Type u} → α → f β → f α :=
    fun {α β} => Functor.map ∘ Function.const β
  Pure.pure : {α : Type u} → α → f α
  Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α :=
    fun {α β} a b => Function.const β <$> a <*> b ()
  SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β :=
    fun {α β} a b => Function.const α id <$> a <*> b ()
constructor:
  Applicative.mk.{u, v} {f : Type u → Type v} [toFunctor : Functor f] [toPure : Pure f] [toSeq : Seq f]
    [toSeqLeft : SeqLeft f] [toSeqRight : SeqRight f] : Applicative f
field notation resolution order:
  Applicative, Functor, Pure, Seq, SeqLeft, SeqRight
-/
#guard_msgs in
#print Applicative

/-! Structure with unused parameter -/

structure Weird (α β : Type _) where
  a : α

/--
info: structure Weird.{u_1, u_2} (α : Type u_1) (β : Type u_2) : Type u_1
number of parameters: 2
fields:
  Weird.a : α
constructor:
  Weird.mk.{u_1, u_2} {α : Type u_1} {β : Type u_2} (a : α) : Weird α β
-/
#guard_msgs in
#print Weird

/-! Structure-like inductive -/

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

#print Nat

private def foo (x : Nat) : Nat := x + 1

/-- info: hello -/
#guard_msgs in #print "hello"
/--
info: def id.{u} : {α : Sort u} → α → α :=
fun {α} a => a
-/
#guard_msgs in #print id
/-- info: axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b -/
#guard_msgs in #print propext
/--
info: def Inhabited.default.{u} : {α : Sort u} → [self : Inhabited α] → α :=
fun α [self : Inhabited α] => self.1
-/
#guard_msgs in #print default
/--
info: protected def ReaderT.read.{u, v} : {ρ : Type u} → {m : Type u → Type v} → [Monad m] → ReaderT ρ m ρ :=
fun {ρ} {m} [Monad m] => pure
-/
#guard_msgs in #print ReaderT.read
/--
info: structure Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
number of parameters: 2
fields:
  Prod.fst : α
  Prod.snd : β
constructor:
  Prod.mk.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) : α × β
-/
#guard_msgs in #print Prod
/-- info: constructor Prod.mk.{u, v} : {α : Type u} → {β : Type v} → α → β → α × β -/
#guard_msgs in #print Prod.mk
/--
info: inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/
#guard_msgs in #print Nat
/-- info: constructor Nat.succ : Nat → Nat -/
#guard_msgs in #print Nat.succ
/--
info: recursor Nat.rec.{u} : {motive : Nat → Sort u} →
  motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
-/
#guard_msgs in #print Nat.rec
/--
info: @[reducible] def Nat.casesOn.{u} : {motive : Nat → Sort u} →
  (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t :=
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
-/
#guard_msgs in #print Nat.casesOn
/--
info: private def foo : Nat → Nat :=
fun x => x + 1
-/
#guard_msgs in #print foo
/-- info: Quotient primitive Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot r -/
#guard_msgs in #print Quot.mk
/--
info: Quotient primitive Quot.ind.{u} : ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
  (∀ (a : α), β (Quot.mk r a)) → ∀ (q : Quot r), β q
-/
#guard_msgs in #print Quot.ind
/-- info: Quotient primitive Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot r -/
#guard_msgs in #print Quot.mk

/-!
Structure with diamond inheritance
-/
structure A where
  a : Nat
structure B extends A where
  b : Nat
structure C extends A where
  c : Nat
structure D extends B, C where
  d : Nat

/--
info: structure D : Type
number of parameters: 0
parents:
  D.toB : B
  D.toC : C
fields:
  A.a : Nat
  B.b : Nat
  C.c : Nat
  D.d : Nat
constructor:
  D.mk (toB : B) (c d : Nat) : D
field notation resolution order:
  D, B, C, A
-/
#guard_msgs in #print D

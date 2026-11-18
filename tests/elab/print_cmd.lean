#print Nat

private def foo (x : Nat) : Nat := x + 1

/-- info: hello -/
#guard_msgs in #print "hello"
/--
info: @[implicit_reducible] def id.{u} : {α : Sort u} → α → α :=
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

section recursors

/-! Basic recursive type -/
/--
info: recursor Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero) (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) : motive t
number of parameters: 0
number of motives: 1 (position 1)
number of minor premises: 2 (positions 2–3)
number of indices: 0
major premise position: 4
rules:
  Nat.rec zero succ Nat.zero
    ==> zero
  Nat.rec zero succ n.succ
    ==> succ n (Nat.rec zero succ n)
-/
#guard_msgs in #print Nat.rec

/-! Recursive structure pretty prints rule with structure instance notation. -/
structure RecStruct (α : Type) where
  val : α
  nChildren : Nat
  children : Fin nChildren → RecStruct α
/--
info: recursor RecStruct.rec.{u} {α : Type} {motive : RecStruct α → Sort u}
  (mk :
    (val : α) →
      (nChildren : Nat) →
        (children : Fin nChildren → RecStruct α) →
          ((a : Fin nChildren) → motive (children a)) →
            motive { val := val, nChildren := nChildren, children := children })
  (t : RecStruct α) : motive t
number of parameters: 1 (position 1)
number of motives: 1 (position 2)
number of minor premises: 1 (position 3)
number of indices: 0
major premise position: 4
rules:
  RecStruct.rec mk { val := val, nChildren := nChildren, children := children }
    ==> mk val nChildren children fun a => RecStruct.rec mk (children a)
-/
#guard_msgs in #print RecStruct.rec


/-! Recursive inductive predicate, with indices and parameters -/
/--
info: recursor Acc.rec.{u_1, u} {α : Sort u} {r : α → α → Prop} {motive : (a : α) → Acc r a → Sort u_1}
  (intro : (x : α) → (h : ∀ (y : α), r y x → Acc r y) → ((y : α) → (a : r y x) → motive y ⋯) → motive x ⋯) {a✝ : α}
  (t : Acc r a✝) : motive a✝ t
number of parameters: 2 (positions 1–2)
number of motives: 1 (position 3)
number of minor premises: 1 (position 4)
number of indices: 1 (position 5)
major premise position: 6
rules:
  Acc.rec intro (Acc.intro x h)
    ==> intro x h fun y a => Acc.rec intro (h y a)
-/
#guard_msgs in #print Acc.rec

/-! Inductive predicate -/
/--
info: recursor And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u} (intro : (left : a) → (right : b) → motive ⋯) (t : a ∧ b) :
  motive t
number of parameters: 2 (positions 1–2)
number of motives: 1 (position 3)
number of minor premises: 1 (position 4)
number of indices: 0
major premise position: 5
rules:
  And.rec intro ⟨left, right⟩
    ==> intro left right
-/
#guard_msgs in #print And.rec

/-! No rules -/
/--
info: recursor False.rec.{u} (motive : False → Sort u) (t : False) : motive t
number of parameters: 0
number of motives: 1 (position 1)
number of minor premises: 0
number of indices: 0
major premise position: 2
rules: (none)
-/
#guard_msgs in #print False.rec

/-! K-like reduction -/
/--
info: recursor True.rec.{u} {motive : True → Sort u} (intro : motive True.intro) (t : True) : motive t
number of parameters: 0
number of motives: 1 (position 1)
number of minor premises: 1 (position 2)
number of indices: 0
major premise position: 3
supports K-like reduction
rules:
  True.rec intro True.intro
    ==> intro
-/
#guard_msgs in #print True.rec

/-! K-like reduction, with indices. (Note that `Eq.rec` pretty prints using the notation `▸`.) -/
/--
info: recursor Eq.rec.{u, u_1} {α : Sort u_1} {a✝ : α} {motive : (a : α) → a✝ = a → Sort u} (refl : motive a✝ ⋯) {a✝¹ : α}
  (t : a✝ = a✝¹) : motive a✝¹ t
number of parameters: 2 (positions 1–2)
number of motives: 1 (position 3)
number of minor premises: 1 (position 4)
number of indices: 1 (position 5)
major premise position: 6
supports K-like reduction
rules:
  Eq.refl a✝ ▸ refl
    ==> refl
-/
#guard_msgs in #print Eq.rec

/-! No K-like reduction. (Note: pretty prints constructor with `⟨⟩` notation.) -/
/--
info: recursor And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u} (intro : (left : a) → (right : b) → motive ⋯) (t : a ∧ b) :
  motive t
number of parameters: 2 (positions 1–2)
number of motives: 1 (position 3)
number of minor premises: 1 (position 4)
number of indices: 0
major premise position: 5
rules:
  And.rec intro ⟨left, right⟩
    ==> intro left right
-/
#guard_msgs in #print And.rec

/-! Nested inductive type. -/
inductive MyList (α : Type) where
  | mk (x : Option (α × MyList α))
/--
info: recursor MyList.rec.{u} {α : Type} {motive_1 : MyList α → Sort u} {motive_2 : Option (α × MyList α) → Sort u}
  {motive_3 : α × MyList α → Sort u} (mk : (x : Option (α × MyList α)) → motive_2 x → motive_1 (MyList.mk x))
  (none : motive_2 none) (some : (val : α × MyList α) → motive_3 val → motive_2 (some val)) :
  ((fst : α) → (snd : MyList α) → motive_1 snd → motive_3 (fst, snd)) → (t : MyList α) → motive_1 t
number of parameters: 1 (position 1)
number of motives: 3 (positions 2–4)
number of minor premises: 4 (positions 5–8)
number of indices: 0
major premise position: 9
rules:
  MyList.rec mk✝ none some mk (MyList.mk x)
    ==> mk✝ x (MyList.rec_1 mk✝ none some mk x)
-/
#guard_msgs in #print MyList.rec
/--
info: recursor MyList.rec_1.{u} {α : Type} {motive_1 : MyList α → Sort u} {motive_2 : Option (α × MyList α) → Sort u}
  {motive_3 : α × MyList α → Sort u} (mk : (x : Option (α × MyList α)) → motive_2 x → motive_1 (MyList.mk x))
  (none : motive_2 none) (some : (val : α × MyList α) → motive_3 val → motive_2 (some val)) :
  ((fst : α) → (snd : MyList α) → motive_1 snd → motive_3 (fst, snd)) → (t : Option (α × MyList α)) → motive_2 t
number of parameters: 1 (position 1)
number of motives: 3 (positions 2–4)
number of minor premises: 4 (positions 5–8)
number of indices: 0
major premise position: 9
rules:
  MyList.rec_1 mk✝ none some mk Option.none
    ==> none
  MyList.rec_1 mk✝ none some mk (Option.some val)
    ==> some val (MyList.rec_2 mk✝ none some mk val)
-/
#guard_msgs in #print MyList.rec_1
/--
info: recursor MyList.rec_2.{u} {α : Type} {motive_1 : MyList α → Sort u} {motive_2 : Option (α × MyList α) → Sort u}
  {motive_3 : α × MyList α → Sort u} (mk : (x : Option (α × MyList α)) → motive_2 x → motive_1 (MyList.mk x))
  (none : motive_2 none) (some : (val : α × MyList α) → motive_3 val → motive_2 (some val)) :
  ((fst : α) → (snd : MyList α) → motive_1 snd → motive_3 (fst, snd)) → (t : α × MyList α) → motive_3 t
number of parameters: 1 (position 1)
number of motives: 3 (positions 2–4)
number of minor premises: 4 (positions 5–8)
number of indices: 0
major premise position: 9
rules:
  MyList.rec_2 mk✝ none some mk (fst, snd)
    ==> mk fst snd (MyList.rec mk✝ none some mk snd)
-/
#guard_msgs in #print MyList.rec_2

/-! Nested inductive type with an index. -/
inductive MyVect (α : Type _) : Nat → Type _ where
  | vnil : MyVect α 0
  | vcons {n} (x : α) (xs : MyVect α n) : MyVect α (n + 1)
inductive Nested (α : Type _) where
  | mk (xs : MyVect (Nested α) 2)
/--
info: recursor Nested.rec.{u, u_1} {α : Type u_1} {motive_1 : Nested α → Sort u}
  {motive_2 : (a : Nat) → MyVect (Nested α) a → Sort u}
  (mk : (xs : MyVect (Nested α) 2) → motive_2 2 xs → motive_1 (Nested.mk xs)) (vnil : motive_2 0 MyVect.vnil)
  (vcons :
    {n : Nat} →
      (x : Nested α) → (xs : MyVect (Nested α) n) → motive_1 x → motive_2 n xs → motive_2 (n + 1) (MyVect.vcons x xs))
  (t : Nested α) : motive_1 t
number of parameters: 1 (position 1)
number of motives: 2 (positions 2–3)
number of minor premises: 3 (positions 4–6)
number of indices: 0
major premise position: 7
rules:
  Nested.rec mk vnil vcons (Nested.mk xs)
    ==> mk xs (Nested.rec_1 mk vnil vcons xs)
-/
#guard_msgs in #print Nested.rec
/--
info: recursor Nested.rec_1.{u, u_1} {α : Type u_1} {motive_1 : Nested α → Sort u}
  {motive_2 : (a : Nat) → MyVect (Nested α) a → Sort u}
  (mk : (xs : MyVect (Nested α) 2) → motive_2 2 xs → motive_1 (Nested.mk xs)) (vnil : motive_2 0 MyVect.vnil)
  (vcons :
    {n : Nat} →
      (x : Nested α) → (xs : MyVect (Nested α) n) → motive_1 x → motive_2 n xs → motive_2 (n + 1) (MyVect.vcons x xs))
  {a✝ : Nat} (t : MyVect (Nested α) a✝) : motive_2 a✝ t
number of parameters: 1 (position 1)
number of motives: 2 (positions 2–3)
number of minor premises: 3 (positions 4–6)
number of indices: 1 (position 7)
major premise position: 8
rules:
  Nested.rec_1 mk vnil vcons MyVect.vnil
    ==> vnil
  Nested.rec_1 mk vnil vcons (MyVect.vcons x xs)
    ==> vcons x xs (Nested.rec mk vnil vcons x) (Nested.rec_1 mk vnil vcons xs)
-/
#guard_msgs in #print Nested.rec_1

/-!
Nested inductive type, universe levels of rules are correct.
Should see `List.nil.{0}` and `List.cons.{0}`.
-/
inductive Nested2 : Type where
  | mk (xs : List Nested2)
/--
info: recursor Nested2.rec.{u} {motive_1 : Nested2 → Sort u} {motive_2 : List.{0} Nested2 → Sort u}
  (mk : (xs : List.{0} Nested2) → motive_2 xs → motive_1 (Nested2.mk xs)) (nil : motive_2 List.nil.{0})
  (cons :
    (head : Nested2) → (tail : List.{0} Nested2) → motive_1 head → motive_2 tail → motive_2 (List.cons.{0} head tail))
  (t : Nested2) : motive_1 t
number of parameters: 0
number of motives: 2 (positions 1–2)
number of minor premises: 3 (positions 3–5)
number of indices: 0
major premise position: 6
rules:
  Nested2.rec.{u} mk nil cons (Nested2.mk xs)
    ==> mk xs (Nested2.rec_1.{u} mk nil cons xs)
-/
#guard_msgs in set_option pp.universes true in #print Nested2.rec
/--
info: recursor Nested2.rec_1.{u} {motive_1 : Nested2 → Sort u} {motive_2 : List.{0} Nested2 → Sort u}
  (mk : (xs : List.{0} Nested2) → motive_2 xs → motive_1 (Nested2.mk xs)) (nil : motive_2 List.nil.{0})
  (cons :
    (head : Nested2) → (tail : List.{0} Nested2) → motive_1 head → motive_2 tail → motive_2 (List.cons.{0} head tail))
  (t : List.{0} Nested2) : motive_2 t
number of parameters: 0
number of motives: 2 (positions 1–2)
number of minor premises: 3 (positions 3–5)
number of indices: 0
major premise position: 6
rules:
  Nested2.rec_1.{u} mk nil cons List.nil.{0}
    ==> nil
  Nested2.rec_1.{u} mk nil cons (List.cons.{0} head tail)
    ==> cons head tail (Nested2.rec.{u} mk nil cons head) (Nested2.rec_1.{u} mk nil cons tail)
-/
#guard_msgs in set_option pp.universes true in #print Nested2.rec_1

end recursors

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

/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude

universes u v w

@[inline] def id {α : Sort u} (a : α) : α := a

abbrev Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

abbrev Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun x => a

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u
  | unit : PUnit

/-- An abbreviation for `PUnit.{0}`, its most common instantiation.
    This Type should be preferred over `PUnit` where possible to avoid
    unnecessary universe parameters. -/
abbrev Unit : Type := PUnit

@[matchPattern] abbrev Unit.unit : Unit := PUnit.unit

/-- Auxiliary unsafe constant used by the Compiler when erasing proofs from code. -/
unsafe axiom lcProof {α : Prop} : α

/-- Auxiliary unsafe constant used by the Compiler to mark unreachable code. -/
unsafe axiom lcUnreachable {α : Sort u} : α

inductive True : Prop
  | intro : True

inductive False : Prop

inductive Empty : Type

def Not (a : Prop) : Prop := a → False

@[macroInline] def False.elim {C : Sort u} (h : False) : C :=
  False.rec (fun _ => C) h

@[macroInline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  False.elim (h₂ h₁)

inductive Eq {α : Sort u} (a : α) : α → Prop
  | refl {} : Eq a a

abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  Eq.rec (motive := fun α _ => motive α) m h

@[matchPattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

theorem Eq.symm {α : Sort u} {a b : α} (h : a = b) : b = a :=
  h ▸ rfl

@[macroInline] def cast {α β : Sort u} (h : α = β) (a : α) : β :=
  Eq.rec (motive := fun α _ => α) a h

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl

/-
Initialize the Quotient Module, which effectively adds the following definitions:

constant Quot {α : Sort u} (r : α → α → Prop) : Sort u

constant Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot r

constant Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → Eq (f a) (f b)) → Quot r → β

constant Quot.ind {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
  (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
-/
init_quot

inductive HEq {α : Sort u} (a : α) : {β : Sort u} → β → Prop
  | refl {} : HEq a a

@[matchPattern] def HEq.rfl {α : Sort u} {a : α} : a ≅ a :=
  HEq.refl a

theorem eqOfHEq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b from
    fun α β a b h₁ =>
      HEq.rec (motive := fun {β} (b : β) (h : HEq a b) => (h₂ : Eq α β) → Eq (cast h₂ a) b)
        (fun (h₂ : Eq α α) => rfl)
        h₁
  this α α a a' h rfl

structure Prod (α : Type u) (β : Type v) :=
  (fst : α) (snd : β)

attribute [unbox] Prod

/-- Similar to `Prod`, but `α` and `β` can be propositions.
   We use this Type internally to automatically generate the brecOn recursor. -/
structure PProd (α : Sort u) (β : Sort v) :=
  (fst : α) (snd : β)

/-- Similar to `Prod`, but `α` and `β` are in the same universe. -/
structure MProd (α β : Type u) :=
  (fst : α) (snd : β)

structure And (a b : Prop) : Prop :=
  intro :: (left : a) (right : b)

inductive Or (a b : Prop) : Prop
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

inductive Bool : Type
  | false : Bool
  | true : Bool

export Bool (false true)

/- Remark: Subtype must take a Sort instead of Type because of the axiom strongIndefiniteDescription. -/
structure Subtype {α : Sort u} (p : α → Prop) :=
  (val : α) (property : p val)

/-- Gadget for optional parameter support. -/
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

/-- Gadget for marking output parameters in type classes. -/
@[reducible] def outParam (α : Sort u) : Sort u := α

/-- Auxiliary Declaration used to implement the notation (a : α) -/
@[reducible] def typedExpr (α : Sort u) (a : α) : α := a

/-- Auxiliary Declaration used to implement the named patterns `x@p` -/
@[reducible] def namedPattern {α : Sort u} (x a : α) : α := a

/- Auxiliary axiom used to implement `sorry`. -/
axiom sorryAx (α : Sort u) (synthetic := true) : α

theorem eqFalseOfNeTrue : {b : Bool} → Not (Eq b true) → b = false
  | true, h => False.elim (h rfl)
  | false, h => rfl

theorem eqTrueOfNeFalse : {b : Bool} → Not (Eq b false) → b = true
  | true, h => rfl
  | false, h => False.elim (h rfl)

theorem neFalseOfEqTrue : {b : Bool} → Eq b true → Not (Eq b false)
  | true, _  => fun h => Bool.noConfusion h
  | false, h => Bool.noConfusion h

theorem neTrueOfEqFalse : {b : Bool} → Eq b false → Not (Eq b true)
  | true, h  => Bool.noConfusion h
  | false, _ => fun h => Bool.noConfusion h

class Inhabited (α : Sort u) :=
  mk {} :: (default : α)

constant arbitrary (α : Sort u) [s : Inhabited α] : α :=
  @Inhabited.default α s

instance (α : Sort u) {β : Sort v} [Inhabited β] : Inhabited (α → β) := {
  default := fun _ => arbitrary β
}

instance (α : Sort u) {β : α → Sort v} [(a : α) → Inhabited (β a)] : Inhabited ((a : α) → β a) := {
  default := fun a => arbitrary (β a)
}

/-- Universe lifting operation from Sort to Type -/
structure PLift (α : Sort u) : Type u :=
  up :: (down : α)

/- Bijection between α and PLift α -/
theorem PLift.upDown {α : Sort u} : ∀ (b : PLift α), up (down b) = b
  | up a => rfl

theorem PLift.downUp {α : Sort u} (a : α) : down (up a) = a :=
  rfl

/- Pointed types -/
structure PointedType :=
  (type : Type u)
  (val : type)

instance : Inhabited PointedType.{u} := {
  default := { type := PUnit.{u+1}, val := ⟨⟩ }
}

/-- Universe lifting operation -/
structure ULift.{r, s} (α : Type s) : Type (max s r) :=
  up :: (down : α)

/- Bijection between α and ULift.{v} α -/
theorem ULift.upDown {α : Type u} : ∀ (b : ULift.{v} α), up (down b) = b
  | up a => rfl

theorem ULift.downUp {α : Type u} (a : α) : down (up.{v} a) = a :=
  rfl

class inductive Decidable (p : Prop)
  | isFalse (h : Not p) : Decidable p
  | isTrue  (h : p) : Decidable p

@[inlineIfReduce, nospecialize] def Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
  Decidable.casesOn (motive := fun _ => Bool) h (fun _ => false) (fun _ => true)

export Decidable (isTrue isFalse decide)

abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

abbrev DecidableRel {α : Sort u} (r : α → α → Prop) :=
  (a b : α) → Decidable (r a b)

abbrev DecidableEq (α : Sort u) :=
  (a b : α) → Decidable (Eq a b)

def decEq {α : Sort u} [s : DecidableEq α] (a b : α) : Decidable (Eq a b) :=
  s a b

theorem decideEqTrue : {p : Prop} → [s : Decidable p] → p → Eq (decide p) true
  | _, isTrue  _, _   => rfl
  | _, isFalse h₁, h₂ => absurd h₂ h₁

theorem decideEqFalse : {p : Prop} → [s : Decidable p] → Not p → Eq (decide p) false
  | _, isTrue  h₁, h₂ => absurd h₁ h₂
  | _, isFalse h, _   => rfl

theorem ofDecideEqTrue {p : Prop} [s : Decidable p] : Eq (decide p) true → p := fun h =>
  match s with
  | isTrue  h₁ => h₁
  | isFalse h₁ => absurd h (neTrueOfEqFalse (decideEqFalse h₁))

theorem ofDecideEqFalse {p : Prop} [s : Decidable p] : Eq (decide p) false → Not p := fun h =>
  match s with
  | isTrue  h₁ => absurd h (neFalseOfEqTrue (decideEqTrue h₁))
  | isFalse h₁ => h₁

@[inline] instance : DecidableEq Bool :=
  fun a b => match a, b with
   | false, false => isTrue rfl
   | false, true  => isFalse (fun h => Bool.noConfusion h)
   | true, false  => isFalse (fun h => Bool.noConfusion h)
   | true, true   => isTrue rfl

class BEq      (α : Type u) := (beq : α → α → Bool)

open BEq (beq)

instance {α : Type u} [DecidableEq α] : BEq α :=
  ⟨fun a b => decide (Eq a b)⟩

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[macroInline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t

/- if-then-else -/

@[macroInline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

@[macroInline] instance {p q} [Decidable p] [Decidable q] : Decidable (And p q) :=
  if hp : p then
    if hq : q then
      isTrue ⟨hp, hq⟩
    else
      isFalse (fun h => hq (And.right h))
  else
    isFalse (fun h => hp (And.left h))

@[macroInline] instance {p q} [Decidable p] [Decidable q] : Decidable (Or p q) :=
  if hp : p then
    isTrue (Or.inl hp)
  else if hq : q then
    isTrue (Or.inr hq)
  else
    isFalse fun h => match h with
      | Or.inl h => hp h
      | Or.inr h => hq h

instance {p} [Decidable p] : Decidable (Not p) :=
  if hp : p then isFalse (absurd hp) else isTrue hp

/- Boolean operators -/

@[macroInline] def cond {a : Type u} : Bool → a → a → a
  | true,  x, y => x
  | false, x, y => y

@[macroInline] def or : Bool → Bool → Bool
  | true,  _ => true
  | false, b => b

@[macroInline] def and : Bool → Bool → Bool
  | false, _ => false
  | true,  b => b

@[macroInline] def not : Bool → Bool
  | true  => false
  | false => true

inductive Nat
  | zero : Nat
  | succ (n : Nat) : Nat

/- For numeric literals notation -/
class OfNat (α : Type u) :=
  (ofNat : Nat → α)

export OfNat (ofNat)

instance : OfNat Nat := ⟨id⟩

instance : Inhabited Nat := {
  default := 0
}

class HasLessEq (α : Type u) := (LessEq : α → α → Prop)
class HasLess   (α : Type u) := (Less : α → α → Prop)

export HasLess (Less)
export HasLessEq (LessEq)

class Add     (α : Type u) := (add : α → α → α)
class Mul     (α : Type u) := (mul : α → α → α)
class Neg     (α : Type u) := (neg : α → α)
class Sub     (α : Type u) := (sub : α → α → α)
class Div     (α : Type u) := (div : α → α → α)
class Mod     (α : Type u) := (mod : α → α → α)
class ModN    (α : Type u) := (modn : α → Nat → α)
class Pow     (α : Type u) (β : Type v) := (pow : α → β → α)
class Append  (α : Type u) := (append : α → α → α)
class OrElse  (α : Type u) := (orElse  : α → α → α)
class AndThen (α : Type u) := (andThen : α → α → α)

open Add (add)
open Mul (mul)
open Pow (pow)
open Append (append)

@[reducible] def GreaterEq {α : Type u} [HasLessEq α] (a b : α) : Prop := LessEq b a
@[reducible] def Greater {α : Type u} [HasLess α] (a b : α) : Prop     := Less b a

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

instance : Add Nat := {
  add := Nat.add
}

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_mul"]
protected def Nat.mul : (@& Nat) → (@& Nat) → Nat
  | a, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

instance : Mul Nat := {
  mul := Nat.mul
}

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_pow"]
protected def Nat.pow (m : @& Nat) : (@& Nat) → Nat
  | 0      => 1
  | succ n => Nat.mul (Nat.pow m n) m

instance : Pow Nat Nat := {
  pow := Nat.pow
}

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_dec_eq"]
def Nat.beq : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ m => false
  | succ n, zero   => false
  | succ n, succ m => beq n m

theorem Nat.eqOfBeqEqTt : {n m : Nat} → Eq (beq n m) true → Eq n m
  | zero,   zero,   h => rfl
  | zero,   succ m, h => Bool.noConfusion h
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have Eq (beq n m) true from h
    have Eq n m from eqOfBeqEqTt this
    this ▸ rfl

theorem Nat.neOfBeqEqFf : {n m : Nat} → Eq (beq n m) false → Not (Eq n m)
  | zero,   zero,   h₁, h₂ => Bool.noConfusion h₁
  | zero,   succ m, h₁, h₂ => Nat.noConfusion h₂
  | succ n, zero,   h₁, h₂ => Nat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have beq n m = false from h₁
    Nat.noConfusion h₂ (fun h₂ => absurd h₂ (neOfBeqEqFf this))

@[extern "lean_nat_dec_eq"]
protected def Nat.decEq (n m : @& Nat) : Decidable (n = m) :=
  if h : beq n m = true then isTrue (eqOfBeqEqTt h)
  else isFalse (neOfBeqEqFf (eqFalseOfNeTrue h))

@[inline] instance : DecidableEq Nat := Nat.decEq

set_option bootstrap.gen_matcher_code false in
@[extern "lean_nat_dec_le"]
def Nat.ble : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ m => true
  | succ n, zero   => false
  | succ n, succ m => ble n m

protected def Nat.le (n m : Nat) : Prop :=
  ble n m = true

instance : HasLessEq Nat := ⟨Nat.le⟩

protected def Nat.lt (n m : Nat) : Prop :=
  Nat.le (succ n) m

instance : HasLess Nat := ⟨Nat.lt⟩

theorem Nat.notSuccLeZero : ∀ (n : Nat), LessEq (succ n) 0 → False
  | 0,      h => nomatch h
  | succ n, h => nomatch h

theorem Nat.notLtZero (n : Nat) : Not (Less n 0) :=
  notSuccLeZero n

@[extern "lean_nat_dec_le"]
instance Nat.decLe (n m : @& Nat) : Decidable (LessEq n m) :=
  decEq (Nat.ble n m) true

@[extern "lean_nat_dec_lt"]
instance Nat.decLt (n m : @& Nat) : Decidable (Less n m) :=
  decLe (succ n) m

theorem Nat.zeroLe : (n : Nat) → LessEq 0 n
  | zero   => rfl
  | succ n => rfl

theorem Nat.succLeSucc {n m : Nat} (h : LessEq n m) : LessEq (succ n) (succ m) :=
  h

theorem Nat.zeroLtSucc (n : Nat) : Less 0 (succ n) :=
  succLeSucc (zeroLe n)

theorem Nat.leStep : {n m : Nat} → LessEq n m → LessEq n (succ m)
  | zero,   zero,   h => rfl
  | zero,   succ n, h => rfl
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have LessEq n m from h
    have LessEq n (succ m) from leStep this
    succLeSucc this

protected theorem Nat.leTrans : {n m k : Nat} → LessEq n m → LessEq m k → LessEq n k
  | zero,   m,      k,      h₁, h₂ => zeroLe _
  | succ n, zero,   k,      h₁, h₂ => Bool.noConfusion h₁
  | succ n, succ m, zero,   h₁, h₂ => Bool.noConfusion h₂
  | succ n, succ m, succ k, h₁, h₂ =>
    have h₁' : LessEq n m from h₁
    have h₂' : LessEq m k from h₂
    Nat.leTrans h₁' h₂'

protected theorem Nat.ltTrans {n m k : Nat} (h₁ : Less n m) : Less m k → Less n k :=
  Nat.leTrans (leStep h₁)

theorem Nat.leSucc : (n : Nat) → LessEq n (succ n)
  | zero   => rfl
  | succ n => leSucc n

theorem Nat.leSuccOfLe {n m : Nat} (h : LessEq n m) : LessEq n (succ m) :=
  Nat.leTrans h (leSucc m)

protected theorem Nat.eqOrLtOfLe : {n m: Nat} → LessEq n m → Or (Eq n m) (Less n m)
  | zero,   zero,   h => Or.inl rfl
  | zero,   succ n, h => Or.inr (zeroLe n)
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have LessEq n m from h
    match Nat.eqOrLtOfLe this with
    | Or.inl h => Or.inl (h ▸ rfl)
    | Or.inr h => Or.inr (succLeSucc h)

protected def Nat.leRefl : (n : Nat) → LessEq n n
  | zero   => rfl
  | succ n => Nat.leRefl n

protected theorem Nat.ltOrGe (n m : Nat) : Or (Less n m) (GreaterEq n m) :=
  match m with
  | zero   => Or.inr (zeroLe n)
  | succ m =>
    match Nat.ltOrGe n m with
    | Or.inl h => Or.inl (leSuccOfLe h)
    | Or.inr h =>
      match Nat.eqOrLtOfLe h with
      | Or.inl h1 => Or.inl (h1 ▸ Nat.leRefl _)
      | Or.inr h1 => Or.inr h1

protected theorem Nat.leAntisymm : {n m : Nat} → LessEq n m → LessEq m n → Eq n m
  | zero,   zero,   h₁, h₂ => rfl
  | succ n, zero,   h₁, h₂ => Bool.noConfusion h₁
  | zero,   succ m, h₁, h₂ => Bool.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have h₁' : LessEq n m from h₁
    have h₂' : LessEq m n from h₂
    (Nat.leAntisymm h₁' h₂') ▸ rfl

protected theorem Nat.ltOfLeOfNe {n m : Nat} (h₁ : LessEq n m) (h₂ : Not (Eq n m)) : Less n m :=
  match Nat.ltOrGe n m with
  | Or.inl h₃ => h₃
  | Or.inr h₃ => absurd (Nat.leAntisymm h₁ h₃) h₂

set_option bootstrap.gen_matcher_code false in
@[extern c inline "lean_nat_sub(#1, lean_box(1))"]
def Nat.pred : Nat → Nat
  | 0      => 0
  | succ a => a

theorem Nat.predLePred : {n m : Nat} → LessEq n m → LessEq (pred n) (pred m)
  | zero,   zero,   h => rfl
  | zero,   succ n, h => zeroLe n
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h => h

theorem Nat.leOfSuccLeSucc {n m : Nat} : LessEq (succ n) (succ m) → LessEq n m :=
  predLePred

theorem Nat.leOfLtSucc {m n : Nat} : Less m (succ n) → LessEq m n :=
  leOfSuccLeSucc

@[extern "lean_system_platform_nbits"] constant System.Platform.getNumBits : Unit → { n : Nat // Or (Eq n 32) (Eq n 64) } :=
  fun _ => ⟨64, Or.inr rfl⟩ -- inhabitant

def System.Platform.numBits : Nat :=
  (getNumBits ()).val

theorem System.Platform.numBitsEq : Or (Eq numBits 32) (Eq numBits 64) :=
  (getNumBits ()).property

structure Fin (n : Nat) :=
  (val  : Nat)
  (isLt : Less val n)

theorem Fin.eqOfVeq {n} : ∀ {i j : Fin n}, Eq i.val j.val → Eq i j
  | ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

theorem Fin.veqOfEq {n} {i j : Fin n} (h : Eq i j) : i.val = j.val :=
  h ▸ rfl

theorem Fin.neOfVne {n} {i j : Fin n} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (veqOfEq h') h

instance (n : Nat) : DecidableEq (Fin n) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (Fin.eqOfVeq h)
    | isFalse h => isFalse (Fin.neOfVne h)

def uint8Sz : Nat := 256
structure UInt8 :=
  (val : Fin uint8Sz)

set_option bootstrap.gen_matcher_code false in
@[extern c inline "#1 == #2"]
def UInt8.decEq (a b : UInt8) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => if h : Eq n m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt8.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq UInt8 := UInt8.decEq

instance : Inhabited UInt8 := {
  default := { val := { val := 0, isLt := decide! } }
}

def uint16Sz : Nat := 65536
structure UInt16 :=
  (val : Fin uint16Sz)

set_option bootstrap.gen_matcher_code false in
@[extern c inline "#1 == #2"]
def UInt16.decEq (a b : UInt16) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => if h : Eq n m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt16.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq UInt16 := UInt16.decEq

instance : Inhabited UInt16 := {
  default := { val := { val := 0, isLt := decide! } }
}

def uint32Sz : Nat := 4294967296
structure UInt32 :=
  (val : Fin uint32Sz)

set_option bootstrap.gen_matcher_code false in
@[extern c inline "#1 == #2"]
def UInt32.decEq (a b : UInt32) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => if h : Eq n m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt32.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq UInt32 := UInt32.decEq

instance : Inhabited UInt32 := {
  default := { val := { val := 0, isLt := decide! } }
}

def uint64Sz : Nat := 18446744073709551616
structure UInt64 :=
  (val : Fin uint64Sz)

set_option bootstrap.gen_matcher_code false in
@[extern c inline "#1 == #2"]
def UInt64.decEq (a b : UInt64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => if h : Eq n m then isTrue (h ▸ rfl) else isFalse (fun h' => UInt64.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq UInt64 := UInt64.decEq

instance : Inhabited UInt64 := {
  default := { val := { val := 0, isLt := decide! } }
}

def usizeSz : Nat := pow 2 System.Platform.numBits

theorem usizeSzEq : Or (Eq usizeSz 4294967296) (Eq usizeSz 18446744073709551616) :=
  show Or (Eq (pow 2 System.Platform.numBits) 4294967296) (Eq (pow 2 System.Platform.numBits) 18446744073709551616) from
  match System.Platform.numBits, System.Platform.numBitsEq with
  | _, Or.inl rfl => Or.inl (decide! : (Eq (pow 2 32) (4294967296:Nat)))
  | _, Or.inr rfl => Or.inr (decide! : (Eq (pow 2 64) (18446744073709551616:Nat)))

structure USize :=
  (val : Fin usizeSz)

set_option bootstrap.gen_matcher_code false in
@[extern c inline "#1 == #2"]
def USize.decEq (a b : USize) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => if h : Eq n m then isTrue (h ▸ rfl) else isFalse (fun h' => USize.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq USize := USize.decEq

instance : Inhabited USize := {
  default := { val := { val := 0, isLt := match usizeSz, usizeSzEq with | _, Or.inl rfl => decide! | _, Or.inr rfl => decide! } }
}

@[extern "lean_usize_of_nat"]
def USize.ofNat32 (n : @& Nat) (h : Less n 4294967296) : USize := {
  val := {
    val  := n,
    isLt := match usizeSz, usizeSzEq with
      | _, Or.inl rfl => h
      | _, Or.inr rfl => Nat.ltTrans h (decide! : Less 4294967296 18446744073709551616)
  }
}

@[extern "lean_usize_of_nat"]
def USize.ofNatCore (n : @& Nat) (h : Less n usizeSz) : USize := {
  val := { val := n, isLt := h }
}

abbrev Nat.isValidChar (n : Nat) : Prop :=
  Or (Less n 0xd800) (And (Less 0xdfff n) (Less n 0x110000))

abbrev UInt32.isValidChar (n : UInt32) : Prop :=
  n.val.val.isValidChar

/-- The `Char` Type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure Char :=
  (val   : UInt32)
  (valid : val.isValidChar)

private theorem validCharIsUInt32 {n : Nat} (h : n.isValidChar) : Less n uint32Sz :=
  match h with
  | Or.inl h      => Nat.ltTrans h (decide! : Less 55296 uint32Sz)
  | Or.inr ⟨_, h⟩ => Nat.ltTrans h (decide! : Less 1114112 uint32Sz)

abbrev Char.ofNat (n : Nat) : Char :=
  if h : n.isValidChar then
    { val := ⟨{ val := n, isLt := validCharIsUInt32 h }⟩, valid := h }
  else
    { val := ⟨{ val := 0, isLt := decide! }⟩, valid := Or.inl decide! }

theorem Char.eqOfVeq : ∀ {c d : Char}, Eq c.val d.val → Eq c d
  | ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

theorem Char.veqOfEq : ∀ {c d : Char}, Eq c d → Eq c.val d.val
  | _, _, rfl => rfl

theorem Char.neOfVne {c d : Char} (h : Not (Eq c.val d.val)) : Not (Eq c d) :=
  fun h' => absurd (veqOfEq h') h

theorem Char.vneOfNe {c d : Char} (h : Not (Eq c d)) : Not (Eq c.val d.val) :=
  fun h' => absurd (eqOfVeq h') h

instance : DecidableEq Char :=
  fun c d =>
    match decEq c.val d.val with
    | isTrue h  => isTrue (Char.eqOfVeq h)
    | isFalse h => isFalse (Char.neOfVne h)

inductive Option (α : Type u)
  | none : Option α
  | some (val : α) : Option α

attribute [unbox] Option

export Option (none some)

instance {α} : Inhabited (Option α) := {
  default := none
}

inductive List (α : Type u)
  | nil : List α
  | cons (head : α) (tail : List α) : List α

instance {α} : Inhabited (List α) := {
  default := List.nil
}

protected def List.hasDecEq {α: Type u} [DecidableEq α] : (a b : List α) → Decidable (Eq a b)
  | nil,       nil       => isTrue rfl
  | cons a as, nil       => isFalse (fun h => List.noConfusion h)
  | nil,       cons b bs => isFalse (fun h => List.noConfusion h)
  | cons a as, cons b bs =>
    match decEq a b with
    | isTrue hab  =>
      match List.hasDecEq as bs with
      | isTrue habs  => isTrue (hab ▸ habs ▸ rfl)
      | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
    | isFalse nab => isFalse (fun h => List.noConfusion h (fun hab _ => absurd hab nab))

instance {α : Type u} [DecidableEq α] : DecidableEq (List α) := List.hasDecEq

@[specialize]
def List.foldl {α β} (f : α → β → α) : (init : α) → List β → α
  | a, nil      => a
  | a, cons b l => foldl f (f a b) l

structure String :=
  (data : List Char)

attribute [extern "lean_string_mk"] String.mk
attribute [extern "lean_string_data"] String.data

@[extern "lean_string_dec_eq"]
def String.decEq (s₁ s₂ : @& String) : Decidable (s₁ = s₂) :=
  match s₁, s₂ with
  | ⟨s₁⟩, ⟨s₂⟩ =>
   if h : s₁ = s₂ then isTrue (congrArg _ h)
   else isFalse (fun h' => String.noConfusion h' (fun h' => absurd h' h))

instance : DecidableEq String := String.decEq

/-- A byte position in a `String`. Internally, `String`s are UTF-8 encoded.
Codepoint positions (counting the Unicode codepoints rather than bytes)
are represented by plain `Nat`s instead.
Indexing a `String` by a byte position is constant-time, while codepoint
positions need to be translated internally to byte positions in linear-time. -/
abbrev String.Pos := Nat

structure Substring :=
  (str : String)
  (startPos : String.Pos)
  (stopPos : String.Pos)

@[extern c inline "#3"]
unsafe def unsafeCast {α : Type u} {β : Type v} (a : α) : β :=
  cast lcProof (PUnit.{v})

@[neverExtract, extern "lean_panic_fn"]
constant panic {α : Type u} [Inhabited α] (msg : String) : α

/-
The Compiler has special support for arrays.
They are implemented using dynamic arrays: https://en.wikipedia.org/wiki/Dynamic_array
-/
structure Array (α : Type u) :=
  (sz   : Nat)
  (data : Fin sz → α)

attribute [extern "lean_array_mk"] Array.mk
attribute [extern "lean_array_data"] Array.data
attribute [extern "lean_array_sz"] Array.sz

/- The parameter `c` is the initial capacity -/
@[extern "lean_mk_empty_array_with_capacity"]
def Array.mkEmpty {α : Type u} (c : @& Nat) : Array α := {
  sz   := 0,
  data := fun ⟨x, h⟩ => absurd h (Nat.notLtZero x)
}

def Array.empty {α : Type u} : Array α :=
  mkEmpty 0

@[reducible, extern "lean_array_get_size"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
  a.sz

@[extern "lean_array_fget"]
def Array.get {α : Type u} (a : @& Array α) (i : @& Fin a.size) : α :=
  a.data i

/- "Comfortable" version of `fget`. It performs a bound check at runtime. -/
@[extern "lean_array_get"]
def Array.get! {α : Type u} [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
  if h : Less i a.size then a.get ⟨i, h⟩ else arbitrary α

@[extern "lean_array_push"]
def push {α : Type u} (a : Array α) (v : α) : Array α := {
  sz   := Nat.succ a.sz,
  data := fun ⟨j, h₁⟩ =>
    if h₂ : j = a.sz then
      v
    else
      a.data ⟨j, Nat.ltOfLeOfNe (Nat.leOfLtSucc h₁) h₂⟩
}

class Bind (m : Type u → Type v) :=
  (bind : {α β : Type u} → m α → (α → m β) → m β)

export Bind (bind)

class Pure (f : Type u → Type v) :=
  (pure {α : Type u} : α → f α)

export Pure (pure)

class Functor (f : Type u → Type v) : Type (max (u+1) v) :=
  (map      : {α β : Type u} → (α → β) → f α → f β)
  (mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _))

class Seq (f : Type u → Type v) : Type (max (u+1) v) :=
  (seq  : {α β : Type u} → f (α → β) → f α → f β)

class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) :=
  (seqLeft : {α : Type u} → f α → f PUnit → f α)

class SeqRight (f : Type u → Type v) : Type (max (u+1) v) :=
  (seqRight : {β : Type u} → f PUnit → f β → f β)

class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f :=
  (map      := fun x y => Seq.seq (pure x) y)
  (seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b)
  (seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b)

class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) :=
  (map      := fun f x => bind x (Function.comp pure f))
  (seq      := fun f x => bind f (fun y => Functor.map y x))
  (seqLeft  := fun x y => bind x (fun a => bind y (fun _ => pure a)))
  (seqRight := fun x y => bind x (fun _ => y))

instance {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) := ⟨pure⟩

instance {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) := ⟨pure $ arbitrary _⟩

/-- A Function for lifting a computation from an inner Monad to an outer Monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class MonadLift (m : Type u → Type v) (n : Type u → Type w) :=
  (monadLift : {α : Type u} → m α → n α)

/-- The reflexive-transitive closure of `MonadLift`.
    `monadLift` is used to transitively lift monadic computations such as `StateT.get` or `StateT.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) :=
  (monadLift : {α : Type u} → m α → n α)

export MonadLiftT (monadLift)

abbrev liftM := @monadLift

instance (m n o) [MonadLiftT m n] [MonadLift n o] : MonadLiftT m o := {
  monadLift := fun x => MonadLift.monadLift (m := n) (monadLift x)
}

instance (m) : MonadLiftT m m := {
  monadLift := fun x => x
}

/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor). -/
class MonadFunctor (m : Type u → Type v) (n : Type u → Type w) :=
  (monadMap {α : Type u} : (∀ {β}, m β → m β) → n α → n α)

/-- The reflexive-transitive closure of `MonadFunctor`.
    `monadMap` is used to transitively lift Monad morphisms -/
class MonadFunctorT (m : Type u → Type v) (n : Type u → Type w) :=
  (monadMap {α : Type u} : (∀ {β}, m β → m β) → n α → n α)

export MonadFunctorT (monadMap)

instance (m n o) [MonadFunctorT m n] [MonadFunctor n o] : MonadFunctorT m o := {
  monadMap := fun f => MonadFunctor.monadMap (m := n) (monadMap (m := m) f)
}

instance monadFunctorRefl (m) : MonadFunctorT m m := {
  monadMap := fun f => f
}

inductive Except (ε : Type u) (α : Type v)
  | error : ε → Except ε α
  | ok    : α → Except ε α

attribute [unbox] Except

instance {ε : Type u} {α : Type v} [Inhabited ε] : Inhabited (Except ε α) :=
  ⟨Except.error (arbitrary ε)⟩

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class MonadExceptOf (ε : Type u) (m : Type v → Type w) :=
  (throw {α : Type v} : ε → m α)
  (tryCatch {α : Type v} : m α → (ε → m α) → m α)

abbrev throwThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (e : ε) : m α :=
  MonadExceptOf.throw e

abbrev tryCatchThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (x : m α) (handle : ε → m α) : m α :=
  MonadExceptOf.tryCatch x handle

/-- Similar to `MonadExceptOf`, but `ε` is an outParam for convenience -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) :=
  (throw {α : Type v} : ε → m α)
  (tryCatch {α : Type v} : m α → (ε → m α) → m α)

export MonadExcept (throw tryCatch)

instance (ε : outParam (Type u)) (m : Type v → Type w) [MonadExceptOf ε m] : MonadExcept ε m := {
  throw    := throwThe ε,
  tryCatch := tryCatchThe ε
}

namespace MonadExcept
variables {ε : Type u} {m : Type v → Type w}

@[inline] protected def orelse [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
  tryCatch t₁ fun _ => t₂

instance [MonadExcept ε m] {α : Type v} : OrElse (m α) := ⟨MonadExcept.orelse⟩

end MonadExcept

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α

instance (ρ : Type u) (m : Type u → Type v) (α : Type u) [Inhabited (m α)] : Inhabited (ReaderT ρ m α) :=
  ⟨fun _ => arbitrary _⟩

@[inline] def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

@[reducible] def Reader (ρ : Type u) := ReaderT ρ id

namespace ReaderT

section
variables {ρ : Type u} {m : Type u → Type v} {α : Type u}

@[inline] protected def lift  (a : m α) : ReaderT ρ m α :=
  fun r => a

instance  : MonadLift m (ReaderT ρ m) := ⟨ReaderT.lift⟩

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ReaderT ρ m) := {
  throw    := Function.comp ReaderT.lift (throwThe ε),
  tryCatch := fun x c r => tryCatchThe ε (x r) (fun e => (c e) r)
}

end

section
variables {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def read : ReaderT ρ m ρ :=
  pure

@[inline] protected def pure (a : α) : ReaderT ρ m α :=
  fun r => pure a

@[inline] protected def bind (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
  fun r => bind (x r) fun a => f a r

@[inline] protected def map (f : α → β) (x : ReaderT ρ m α) : ReaderT ρ m β :=
  fun r => Functor.map f (x r)

instance : Monad (ReaderT ρ m) := {
  pure := ReaderT.pure,
  bind := ReaderT.bind,
  map  := ReaderT.map
}

instance (ρ m) [Monad m] : MonadFunctor m (ReaderT ρ m) := ⟨fun f x r => f (x r)⟩

@[inline] protected def adapt {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α :=
  fun x r => x (f r)

end
end ReaderT

/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this Function cannot be lifted using `monadLift`.
    Instead, the `MonadReaderAdapter` class provides the more general `adaptReader` Function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadReader (ρ : outParam (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [Monad m], ReaderT ρ m α) → n α)
    ```
    -/
class MonadReaderOf (ρ : Type u) (m : Type u → Type v) :=
  (read : m ρ)

@[inline] def readThe (ρ : Type u) {m : Type u → Type v} [MonadReaderOf ρ m] : m ρ :=
  MonadReaderOf.read

/-- Similar to `MonadReaderOf`, but `ρ` is an outParam for convenience -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :=
  (read : m ρ)

export MonadReader (read)

instance (ρ : Type u) (m : Type u → Type v) [MonadReaderOf ρ m] : MonadReader ρ m :=
  ⟨readThe ρ⟩

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadReaderOf ρ m] [MonadLift m n] : MonadReaderOf ρ n :=
  ⟨monadLift (MonadReader.read : m ρ)⟩

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReaderOf ρ (ReaderT ρ m) :=
  ⟨ReaderT.read⟩

class MonadWithReaderOf (ρ : Type u) (m : Type u → Type v) :=
  (withReader {α : Type u} : (ρ → ρ) → m α → m α)

@[inline] def withTheReader (ρ : Type u) {m : Type u → Type v} [MonadWithReaderOf ρ m] {α : Type u} (f : ρ → ρ) (x : m α) : m α :=
  MonadWithReaderOf.withReader f x

class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) :=
  (withReader {α : Type u} : (ρ → ρ) → m α → m α)

export MonadWithReader (withReader)

instance (ρ : Type u) (m : Type u → Type v) [MonadWithReaderOf ρ m] : MonadWithReader ρ m := ⟨withTheReader ρ⟩

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type v} [MonadWithReaderOf ρ m] [MonadFunctor m n] : MonadWithReaderOf ρ n :=
  ⟨fun f => monadMap (m := m) (withTheReader ρ f)⟩

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadWithReaderOf ρ (ReaderT ρ m) :=
  ⟨fun f x ctx => x (f ctx)⟩

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class MonadStateOf (σ : Type u) (m : Type u → Type v) :=
  /- Obtain the top-most State of a Monad stack. -/
  (get : m σ)
  /- Set the top-most State of a Monad stack. -/
  (set : σ → m PUnit)
  /- Map the top-most State of a Monad stack.

     Note: `modifyGet f` may be preferable to `do s <- get; let (a, s) := f s; put s; pure a`
     because the latter does not use the State linearly (without sufficient inlining). -/
  (modifyGet {α : Type u} : (σ → α × σ) → m α)

export MonadStateOf (set)

abbrev getThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] : m σ :=
  MonadStateOf.get

@[inline] abbrev modifyThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → σ) : m PUnit :=
  MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

@[inline] abbrev modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → α × σ) : m α :=
  MonadStateOf.modifyGet f

/-- Similar to `MonadStateOf`, but `σ` is an outParam for convenience -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :=
  (get : m σ)
  (set : σ → m PUnit)
  (modifyGet {α : Type u} : (σ → α × σ) → m α)

export MonadState (get modifyGet)

instance (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m := {
  set       := MonadStateOf.set,
  get       := getThe σ,
  modifyGet := fun f => MonadStateOf.modifyGet f
}

@[inline] def modify {σ : Type u} {m : Type u → Type v} [MonadState σ m] (f : σ → σ) : m PUnit :=
  modifyGet fun s => (PUnit.unit, f s)

@[inline] def getModify {σ : Type u} {m : Type u → Type v} [MonadState σ m] [Monad m] (f : σ → σ) : m σ :=
  modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadStateOf σ m] [MonadLift m n] : MonadStateOf σ n := {
  get       := liftM (m := m) MonadStateOf.get,
  set       := fun s => liftM (m := m) (MonadStateOf.set s),
  modifyGet := fun f => monadLift (m := m) (MonadState.modifyGet f)
}

namespace EStateM

inductive Result (ε σ α : Type u)
  | ok    : α → σ → Result ε σ α
  | error : ε → σ → Result ε σ α

variables {ε σ α : Type u}

instance [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) := ⟨Result.error (arbitrary _) (arbitrary _)⟩

end EStateM

open EStateM (Result) in
def EStateM (ε σ α : Type u) := σ → Result ε σ α

namespace EStateM

variables {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EStateM ε σ α) := ⟨fun s =>
  Result.error (arbitrary ε) s⟩

@[inline] protected def pure (a : α) : EStateM ε σ α := fun s =>
  Result.ok a s

@[inline] protected def set (s : σ) : EStateM ε σ PUnit := fun _ =>
  Result.ok ⟨⟩ s

@[inline] protected def get : EStateM ε σ σ := fun s =>
  Result.ok s s

@[inline] protected def modifyGet (f : σ → α × σ) : EStateM ε σ α := fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : EStateM ε σ α := fun s =>
  Result.error e s

/-- Auxiliary instance for saving/restoring the "backtrackable" part of the state. -/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) :=
  (save    : σ → δ)
  (restore : σ → δ → σ)

@[inline] protected def tryCatch {δ} [Backtrackable δ σ] {α} (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s
  match x s with
  | Result.error e s => handle e (Backtrackable.restore s d)
  | ok               => ok

@[inline] protected def orElse {δ} [Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) : EStateM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error _ s => x₂ (Backtrackable.restore s d)
  | ok               => ok

@[inline] def adaptExcept {ε' : Type u} (f : ε → ε') (x : EStateM ε σ α) : EStateM ε' σ α := fun s =>
  match x s with
  | Result.error e s => Result.error (f e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : EStateM ε σ α) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : EStateM ε σ PUnit) (y : EStateM ε σ β) : EStateM ε σ β := fun s =>
  match x s with
  | Result.ok _ s    => y s
  | Result.error e s => Result.error e s

instance : Monad (EStateM ε σ) := {
  bind     := EStateM.bind,
  pure     := EStateM.pure,
  map      := EStateM.map,
  seqRight := EStateM.seqRight
}

instance {δ} [Backtrackable δ σ] : OrElse (EStateM ε σ α) := {
  orElse := EStateM.orElse
}

instance : MonadStateOf σ (EStateM ε σ) := {
  set       := EStateM.set,
  get       := EStateM.get,
  modifyGet := EStateM.modifyGet
}

instance {δ} [Backtrackable δ σ] : MonadExceptOf ε (EStateM ε σ) := {
  throw    := EStateM.throw,
  tryCatch := EStateM.tryCatch
}

@[inline] def run (x : EStateM ε σ α) (s : σ) : Result ε σ α :=
  x s

@[inline] def run' (x : EStateM ε σ α) (s : σ) : Option α :=
  match run x s with
  | Result.ok v _    => some v
  | Result.error _ _ => none

@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ := {
  save    := dummySave,
  restore := dummyRestore
}

end EStateM

class Hashable (α : Type u) :=
  (hash : α → USize)

export Hashable (hash)

@[extern "lean_usize_mix_hash"]
constant mixHash (u₁ u₂ : USize) : USize

@[extern "lean_string_hash"]
protected constant String.hash (s : @& String) : USize

instance : Hashable String := ⟨String.hash⟩

namespace Lean

/- Hierarchical names -/
inductive Name
  | anonymous : Name
  | str : Name → String → USize → Name
  | num : Name → Nat → USize → Name

instance : Inhabited Name := ⟨Name.anonymous⟩

protected def Name.hash : Name → USize
  | Name.anonymous => USize.ofNat32 1723 decide!
  | Name.str p s h => h
  | Name.num p v h => h

instance : Hashable Name := ⟨Name.hash⟩

@[export lean_name_mk_string]
def mkNameStr (p : Name) (s : String) : Name :=
  Name.str p s (mixHash (hash p) (hash s))

@[export lean_name_mk_numeral]
def mkNameNum (p : Name) (v : Nat) : Name :=
  Name.num p v (mixHash (hash p) (if h : Less v usizeSz then USize.ofNatCore v h else USize.ofNat32 17 decide!))

def mkNameSimple (s : String) : Name :=
  mkNameStr Name.anonymous s

namespace Name
@[extern "lean_name_eq"]
protected def beq : (@& Name) → (@& Name) → Bool
  | anonymous,   anonymous   => true
  | str p₁ s₁ _, str p₂ s₂ _ => BEq.beq s₁ s₂ && Name.beq p₁ p₂
  | num p₁ n₁ _, num p₂ n₂ _ => BEq.beq n₁ n₂ && Name.beq p₁ p₂
  | _,           _           => false

instance : BEq Name := ⟨Name.beq⟩

protected def append : Name → Name → Name
  | n, anonymous => n
  | n, str p s _ => mkNameStr (Name.append n p) s
  | n, num p d _ => mkNameNum (Name.append n p) d

instance : Append Name := ⟨Name.append⟩

end Name

/- Syntax -/

/--
  Source information of syntax atoms. All information is generally set for unquoted syntax and unset for syntax in
  syntax quotations, but syntax transformations might want to invalidate only one side to make the pretty printer
  reformat it. In the special case of the delaborator, we also use purely synthetic position information without
  whitespace information. -/
structure SourceInfo :=
  /- Will be inferred after parsing by `Syntax.updateLeading`. During parsing,
     it is not at all clear what the preceding token was, especially with backtracking. -/
  (leading  : Option Substring  := none)
  (pos      : Option String.Pos := none)
  (trailing : Option Substring  := none)

instance : Inhabited SourceInfo := ⟨{}⟩

abbrev SyntaxNodeKind := Name

/- Syntax AST -/

inductive Syntax
  | missing : Syntax
  | node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom   (info : SourceInfo) (val : String) : Syntax
  | ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Prod Name (List String))) : Syntax

instance : Inhabited Syntax := ⟨Syntax.missing⟩

/- Builtin kinds -/
def choiceKind : SyntaxNodeKind := `choice
def nullKind : SyntaxNodeKind := `null
def identKind : SyntaxNodeKind := `ident
def strLitKind : SyntaxNodeKind := `strLit
def charLitKind : SyntaxNodeKind := `charLit
def numLitKind : SyntaxNodeKind := `numLit
def nameLitKind : SyntaxNodeKind := `nameLit
def fieldIdxKind : SyntaxNodeKind := `fieldIdx
def interpolatedStrLitKind : SyntaxNodeKind := `interpolatedStrLitKind
def interpolatedStrKind : SyntaxNodeKind := `interpolatedStrKind

namespace Syntax

def getKind (stx : Syntax) : SyntaxNodeKind :=
  match stx with
  | Syntax.node k args   => k
  -- We use these "pseudo kinds" for antiquotation kinds.
  -- For example, an antiquotation `$id:ident` (using Lean.Parser.Term.ident)
  -- is compiled to ``if stx.isOfKind `ident ...``
  | Syntax.missing       => `missing
  | Syntax.atom _ v      => mkNameSimple v
  | Syntax.ident _ _ _ _ => identKind

def setKind (stx : Syntax) (k : SyntaxNodeKind) : Syntax :=
  match stx with
  | Syntax.node _ args => Syntax.node k args
  | _                  => stx

def isOfKind (stx : Syntax) (k : SyntaxNodeKind) : Bool :=
  beq stx.getKind k

def getArg (stx : Syntax) (i : Nat) : Syntax :=
  match stx with
  | Syntax.node _ args => args.get! i
  | _                  => Syntax.missing -- panic! "Syntax.getArg: not a node"

-- Add `stx[i]` as sugar for `stx.getArg i`
@[inline] def getOp (self : Syntax) (idx : Nat) : Syntax :=
  self.getArg idx

def getArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | Syntax.node _ args => args
  | _                  => Array.empty

end Syntax

inductive ParserDescr
  | andthen           : ParserDescr → ParserDescr → ParserDescr
  | orelse            : ParserDescr → ParserDescr → ParserDescr
  | optional          : ParserDescr → ParserDescr
  | lookahead         : ParserDescr → ParserDescr
  | «try»             : ParserDescr → ParserDescr
  | many              : ParserDescr → ParserDescr
  | many1             : ParserDescr → ParserDescr
  | sepBy             : ParserDescr → ParserDescr → Bool → ParserDescr
  | sepBy1            : ParserDescr → ParserDescr → Bool → ParserDescr
  | node              : Name → Nat → ParserDescr → ParserDescr
  | trailingNode      : Name → Nat → ParserDescr → ParserDescr
  | symbol            : String → ParserDescr
  | nonReservedSymbol : String → Bool → ParserDescr
  | noWs              : ParserDescr
  | numLit            : ParserDescr
  | strLit            : ParserDescr
  | charLit           : ParserDescr
  | nameLit           : ParserDescr
  | interpolatedStr   : ParserDescr → ParserDescr -- interpolated string
  | ident             : ParserDescr
  | cat               : Name → Nat → ParserDescr
  | parser            : Name → ParserDescr
  | notFollowedBy     : ParserDescr → ParserDescr
  | withPosition      : ParserDescr → ParserDescr
  | checkCol          : Bool → ParserDescr

instance : Inhabited ParserDescr := ⟨ParserDescr.symbol ""⟩
abbrev TrailingParserDescr := ParserDescr

/-
Runtime support for making quotation terms auto-hygienic, by mangling identifiers
introduced by them with a "macro scope" supplied by the context. Details to appear in a
paper soon.
-/

abbrev MacroScope := Nat
/-- Macro scope used internally. It is not available for our frontend. -/
def reservedMacroScope := 0
/-- First macro scope available for our frontend -/
def firstFrontendMacroScope := add reservedMacroScope 1

/-- A monad that supports syntax quotations. Syntax quotations (in term
    position) are monadic values that when executed retrieve the current "macro
    scope" from the monad and apply it to every identifier they introduce
    (independent of whether this identifier turns out to be a reference to an
    existing declaration, or an actually fresh binding during further
    elaboration). -/
class MonadQuotation (m : Type → Type) :=
  -- Get the fresh scope of the current macro invocation
  (getCurrMacroScope : m MacroScope)
  (getMainModule     : m Name)
  /- Execute action in a new macro invocation context. This transformer should be
     used at all places that morally qualify as the beginning of a "macro call",
     e.g. `elabCommand` and `elabTerm` in the case of the elaborator. However, it
     can also be used internally inside a "macro" if identifiers introduced by
     e.g. different recursive calls should be independent and not collide. While
     returning an intermediate syntax tree that will recursively be expanded by
     the elaborator can be used for the same effect, doing direct recursion inside
     the macro guarded by this transformer is often easier because one is not
     restricted to passing a single syntax tree. Modelling this helper as a
     transformer and not just a monadic action ensures that the current macro
     scope before the recursive call is restored after it, as expected. -/
  (withFreshMacroScope {α : Type} : m α → m α)

export MonadQuotation (getCurrMacroScope getMainModule withFreshMacroScope)

instance {m n : Type → Type} [MonadQuotation m] [MonadLift m n] [MonadFunctorT m n] : MonadQuotation n := {
  getCurrMacroScope   := liftM (m := m) getCurrMacroScope,
  getMainModule       := liftM (m := m) getMainModule,
  withFreshMacroScope := monadMap (m := m) withFreshMacroScope
}

/-
We represent a name with macro scopes as
```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
Example: suppose the module name is `Init.Data.List.Basic`, and name is `foo.bla`, and macroscopes [2, 5]
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```

We may have to combine scopes from different files/modules.
The main modules being processed is always the right most one.
This situation may happen when we execute a macro generated in
an imported file in the current file.
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```

The delimiter `_hyg` is used just to improve the `hasMacroScopes` performance.
-/

def Name.hasMacroScopes : Name → Bool
  | str _ s _   => beq s "_hyg"
  | num p _   _ => hasMacroScopes p
  | _           => false

private def eraseMacroScopesAux : Name → Name
  | Name.str p s _   => if s = "_@" then p else eraseMacroScopesAux p
  | Name.num p _ _   => eraseMacroScopesAux p
  | Name.anonymous   => Name.anonymous

@[export lean_erase_macro_scopes]
def Name.eraseMacroScopes (n : Name) : Name :=
  match n.hasMacroScopes with
  | true  => eraseMacroScopesAux n
  | false => n

private def simpMacroScopesAux : Name → Name
  | Name.num p i _ => mkNameNum (simpMacroScopesAux p) i
  | n              => eraseMacroScopesAux n

/- Helper function we use to create binder names that do not need to be unique. -/
@[export lean_simp_macro_scopes]
def Name.simpMacroScopes (n : Name) : Name :=
  match n.hasMacroScopes with
  | true  => simpMacroScopesAux n
  | false => n

structure MacroScopesView :=
  (name       : Name)
  (imported   : Name)
  (mainModule : Name)
  (scopes     : List MacroScope)

instance : Inhabited MacroScopesView := ⟨⟨arbitrary _, arbitrary _, arbitrary _, arbitrary _⟩⟩

def MacroScopesView.review (view : MacroScopesView) : Name :=
  match view.scopes with
  | List.nil      => view.name
  | List.cons _ _ =>
    let base := (mkNameStr (append (append (mkNameStr view.name "_@") view.imported) view.mainModule) "_hyg")
    view.scopes.foldl mkNameNum base

private def assembleParts : List Name → Name → Name
  | List.nil,                      acc => acc
  | List.cons (Name.str _ s _) ps, acc => assembleParts ps (mkNameStr acc s)
  | List.cons (Name.num _ n _) ps, acc => assembleParts ps (mkNameNum acc n)
  | _,                             acc => panic "unreachable @ assembleParts"

private def extractImported (scps : List MacroScope) (mainModule : Name) : Name → List Name → MacroScopesView
  | n@(Name.str p str _), parts =>
    if str = "_@" then
      { name := p, mainModule := mainModule, imported := assembleParts parts Name.anonymous, scopes := scps }
    else
      extractImported scps mainModule p (List.cons n parts)
  | n@(Name.num p str _), parts => extractImported scps mainModule p (List.cons n parts)
  | _,                    _     => panic "unreachable @ extractImported"

private def extractMainModule (scps : List MacroScope) : Name → List Name → MacroScopesView
  | n@(Name.str p str _), parts =>
    if str = "_@" then
      { name := p, mainModule := assembleParts parts Name.anonymous, imported := Name.anonymous, scopes := scps }
    else
      extractMainModule scps p (List.cons n parts)
  | n@(Name.num p num _), acc => extractImported scps (assembleParts acc Name.anonymous) n List.nil
  | _,                    _   => panic "unreachable @ extractMainModule"

private def extractMacroScopesAux : Name → List MacroScope → MacroScopesView
  | Name.num p scp _, acc => extractMacroScopesAux p (List.cons scp acc)
  | Name.str p str _, acc => extractMainModule acc p List.nil -- str must be "_hyg"
  | _,                _   => panic "unreachable @ extractMacroScopesAux"

/--
  Revert all `addMacroScope` calls. `v = extractMacroScopes n → n = v.review`.
  This operation is useful for analyzing/transforming the original identifiers, then adding back
  the scopes (via `MacroScopesView.review`). -/
def extractMacroScopes (n : Name) : MacroScopesView :=
  match n.hasMacroScopes with
  | true  => extractMacroScopesAux n List.nil
  | false => { name := n, scopes := List.nil, imported := Name.anonymous, mainModule := Name.anonymous }

def addMacroScope (mainModule : Name) (n : Name) (scp : MacroScope) : Name :=
  match n.hasMacroScopes with
  | true =>
    let view := extractMacroScopes n
    match beq view.mainModule mainModule with
    | true  => mkNameNum n scp
    | false =>
      { view with
        imported   := view.scopes.foldl mkNameNum (append view.imported view.mainModule),
        mainModule := mainModule,
        scopes     := List.cons scp List.nil
      }.review
  | false =>
    mkNameNum (mkNameStr (append (mkNameStr n "_@") mainModule) "_hyg") scp

@[inline] def MonadQuotation.addMacroScope {m : Type → Type} [MonadQuotation m] [Monad m] (n : Name) : m Name :=
  bind getMainModule     fun mainModule =>
  bind getCurrMacroScope fun scp =>
  pure (Lean.addMacroScope mainModule n scp)

def defaultMaxRecDepth := 512

def maxRecDepthErrorMessage : String :=
  "maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)"

namespace Macro

/- References -/
constant MacroEnvPointed : PointedType.{0}

def MacroEnv : Type := MacroEnvPointed.type
instance : Inhabited MacroEnv := ⟨MacroEnvPointed.val⟩

structure Context :=
  (macroEnv       : MacroEnv)
  (mainModule     : Name)
  (currMacroScope : MacroScope)
  (currRecDepth   : Nat := 0)
  (maxRecDepth    : Nat := defaultMaxRecDepth)

inductive Exception
  | error             : Syntax → String → Exception
  | unsupportedSyntax : Exception

end Macro

abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception MacroScope)

abbrev Macro := Syntax → MacroM Syntax

namespace Macro

def addMacroScope (n : Name) : MacroM Name :=
  bind read fun ctx =>
  pure (Lean.addMacroScope ctx.mainModule n ctx.currMacroScope)

def throwUnsupported {α} : MacroM α :=
  throw Exception.unsupportedSyntax

def throwError {α} (ref : Syntax) (msg : String) : MacroM α :=
  throw (Exception.error ref msg)

@[inline] protected def withFreshMacroScope {α} (x : MacroM α) : MacroM α :=
  bind (modifyGet (fun s => (s, add s 1))) fun fresh =>
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : MacroM α) : MacroM α :=
  bind read fun ctx =>
  if ctx.currRecDepth = ctx.maxRecDepth then
    throw (Exception.error ref maxRecDepthErrorMessage)
  else
    withReader (fun ctx => { ctx with currRecDepth := add ctx.currRecDepth 1 }) x

instance : MonadQuotation MacroM := {
  getCurrMacroScope   := fun ctx => pure ctx.currMacroScope,
  getMainModule       := fun ctx => pure ctx.mainModule,
  withFreshMacroScope := Macro.withFreshMacroScope
}

unsafe def mkMacroEnvImp (expandMacro? : Syntax → MacroM (Option Syntax)) : MacroEnv :=
  unsafeCast expandMacro?

@[implementedBy mkMacroEnvImp]
constant mkMacroEnv (expandMacro? : Syntax → MacroM (Option Syntax)) : MacroEnv

def expandMacroNotAvailable? (stx : Syntax) : MacroM (Option Syntax) :=
  throwError stx "expandMacro has not been set"

def mkMacroEnvSimple : MacroEnv :=
  mkMacroEnv expandMacroNotAvailable?

unsafe def expandMacro?Imp (stx : Syntax) : MacroM (Option Syntax) :=
  bind read fun ctx =>
  let f : Syntax → MacroM (Option Syntax) := unsafeCast (ctx.macroEnv)
  f stx

/-- `expandMacro? stx` return `some stxNew` if `stx` is a macro, and `stxNew` is its expansion. -/
@[implementedBy expandMacro?Imp] constant expandMacro? : Syntax → MacroM (Option Syntax)

end Macro

export Macro (expandMacro?)

end Lean

syntax "foo" term : term

macro_rules
  | `(foo $x) => x

#check foo 10

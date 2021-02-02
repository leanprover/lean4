/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude

universes u v w

@[inline] def id {α : Sort u} (a : α) : α := a

/- `idRhs` is an auxiliary declaration used to implement "smart unfolding". It is used as a marker. -/
@[macroInline, reducible] def idRhs (α : Sort u) (a : α) : α := a

abbrev Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

abbrev Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun x => a

@[reducible] def inferInstance {α : Type u} [i : α] : α := i
@[reducible] def inferInstanceAs (α : Type u) [i : α] : α := i

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
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

inductive True : Prop where
  | intro : True

inductive False : Prop

inductive Empty : Type

def Not (a : Prop) : Prop := a → False

@[macroInline] def False.elim {C : Sort u} (h : False) : C :=
  False.rec (fun _ => C) h

@[macroInline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  False.elim (h₂ h₁)

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl {} : Eq a a

abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  Eq.rec (motive := fun α _ => motive α) m h

@[matchPattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  h₂ ▸ h₁

@[macroInline] def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  Eq.rec (motive := fun α _ => α) a h

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl

theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : Eq f₁ f₂) (h₂ : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  h₁ ▸ h₂ ▸ rfl

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) →  β x} (h : Eq f g) (a : α) : Eq (f a) (g a) :=
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

inductive HEq {α : Sort u} (a : α) : {β : Sort u} → β → Prop where
  | refl {} : HEq a a

@[matchPattern] def HEq.rfl {α : Sort u} {a : α} : HEq a a :=
  HEq.refl a

theorem eqOfHEq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b from
    fun α β a b h₁ =>
      HEq.rec (motive := fun {β} (b : β) (h : HEq a b) => (h₂ : Eq α β) → Eq (cast h₂ a) b)
        (fun (h₂ : Eq α α) => rfl)
        h₁
  this α α a a' h rfl

structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

attribute [unbox] Prod

/-- Similar to `Prod`, but `α` and `β` can be propositions.
   We use this Type internally to automatically generate the brecOn recursor. -/
structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

/-- Similar to `Prod`, but `α` and `β` are in the same universe. -/
structure MProd (α β : Type u) where
  fst : α
  snd : β

structure And (a b : Prop) : Prop where
  intro :: (left : a) (right : b)

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

inductive Bool : Type where
  | false : Bool
  | true : Bool

export Bool (false true)

/- Remark: Subtype must take a Sort instead of Type because of the axiom strongIndefiniteDescription. -/
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val

/-- Gadget for optional parameter support. -/
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

/-- Gadget for marking output parameters in type classes. -/
@[reducible] def outParam (α : Sort u) : Sort u := α

/-- Auxiliary Declaration used to implement the notation (a : α) -/
@[reducible] def typedExpr (α : Sort u) (a : α) : α := a

/-- Auxiliary Declaration used to implement the named patterns `x@p` -/
@[reducible] def namedPattern {α : Sort u} (x a : α) : α := a

/- Auxiliary axiom used to implement `sorry`. -/
@[extern "lean_sorry", neverExtract]
axiom sorryAx (α : Sort u) (synthetic := true) : α

theorem eqFalseOfNeTrue : {b : Bool} → Not (Eq b true) → Eq b false
  | true, h => False.elim (h rfl)
  | false, h => rfl

theorem eqTrueOfNeFalse : {b : Bool} → Not (Eq b false) → Eq b true
  | true, h => rfl
  | false, h => False.elim (h rfl)

theorem neFalseOfEqTrue : {b : Bool} → Eq b true → Not (Eq b false)
  | true, _  => fun h => Bool.noConfusion h
  | false, h => Bool.noConfusion h

theorem neTrueOfEqFalse : {b : Bool} → Eq b false → Not (Eq b true)
  | true, h  => Bool.noConfusion h
  | false, _ => fun h => Bool.noConfusion h

class Inhabited (α : Sort u) where
  mk {} :: (default : α)

constant arbitrary [Inhabited α] : α :=
  Inhabited.default

instance : Inhabited (Sort u) where
  default := PUnit

instance (α : Sort u) {β : Sort v} [Inhabited β] : Inhabited (α → β) where
  default := fun _ => arbitrary

instance (α : Sort u) {β : α → Sort v} [(a : α) → Inhabited (β a)] : Inhabited ((a : α) → β a) where
  default := fun _ => arbitrary

/-- Universe lifting operation from Sort to Type -/
structure PLift (α : Sort u) : Type u where
  up :: (down : α)

/- Bijection between α and PLift α -/
theorem PLift.upDown {α : Sort u} : ∀ (b : PLift α), Eq (up (down b)) b
  | up a => rfl

theorem PLift.downUp {α : Sort u} (a : α) : Eq (down (up a)) a :=
  rfl

/- Pointed types -/
structure PointedType where
  (type : Type u)
  (val : type)

instance : Inhabited PointedType.{u} where
  default := { type := PUnit.{u+1}, val := ⟨⟩ }

/-- Universe lifting operation -/
structure ULift.{r, s} (α : Type s) : Type (max s r) where
  up :: (down : α)

/- Bijection between α and ULift.{v} α -/
theorem ULift.upDown {α : Type u} : ∀ (b : ULift.{v} α), Eq (up (down b)) b
  | up a => rfl

theorem ULift.downUp {α : Type u} (a : α) : Eq (down (up.{v} a)) a :=
  rfl

class inductive Decidable (p : Prop) where
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

class BEq (α : Type u) where
  beq : α → α → Bool

open BEq (beq)

instance {α : Type u} [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[macroInline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t

/- if-then-else -/

@[macroInline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

@[macroInline] instance {p q} [dp : Decidable p] [dq : Decidable q] : Decidable (And p q) :=
  match dp with
  | isTrue  hp =>
    match dq with
    | isTrue hq  => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse (fun h => hq (And.right h))
  | isFalse hp =>
    isFalse (fun h => hp (And.left h))

@[macroInline] instance {p q} [dp : Decidable p] [dq : Decidable q] : Decidable (Or p q) :=
  match dp with
  | isTrue  hp => isTrue (Or.inl hp)
  | isFalse hp =>
    match dq with
    | isTrue hq  => isTrue (Or.inr hq)
    | isFalse hq =>
      isFalse fun h => match h with
        | Or.inl h => hp h
        | Or.inr h => hq h

instance {p} [dp : Decidable p] : Decidable (Not p) :=
  match dp with
  | isTrue hp  => isFalse (absurd hp)
  | isFalse hp => isTrue hp

/- Boolean operators -/

@[macroInline] def cond {α : Type u} (c : Bool) (x y : α) : α :=
  match c with
  | true  => x
  | false => y

@[macroInline] def or (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

@[macroInline] def and (x y : Bool) : Bool :=
  match x with
  | false => false
  | true  => y

@[inline] def not : Bool → Bool
  | true  => false
  | false => true

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

instance : Inhabited Nat where
  default := Nat.zero

/- For numeric literals notation -/
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[defaultInstance 100] /- low prio -/
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HasLessEq (α : Type u) where LessEq : α → α → Prop
class HasLess   (α : Type u) where Less : α → α → Prop

export HasLess (Less)
export HasLessEq (LessEq)

class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ

class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSub : α → β → γ

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hDiv : α → β → γ

class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMod : α → β → γ

class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hPow : α → β → γ

class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAppend : α → β → γ

class HOrElse (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hOrElse : α → β → γ

class HAndThen (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAndThen : α → β → γ

class Add (α : Type u) where
  add : α → α → α

class Sub (α : Type u) where
  sub : α → α → α

class Mul (α : Type u) where
  mul : α → α → α

class Neg (α : Type u) where
  neg : α → α

class Div (α : Type u) where
  div : α → α → α

class Mod (α : Type u) where
  mod : α → α → α

class Pow (α : Type u) where
  pow : α → α → α

class Append (α : Type u) where
  append : α → α → α

class OrElse (α : Type u) where
  orElse  : α → α → α

class AndThen (α : Type u) where
  andThen : α → α → α

@[defaultInstance]
instance [Add α] : HAdd α α α where
  hAdd a b := Add.add a b

@[defaultInstance]
instance [Sub α] : HSub α α α where
  hSub a b := Sub.sub a b

@[defaultInstance]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

@[defaultInstance]
instance [Div α] : HDiv α α α where
  hDiv a b := Div.div a b

@[defaultInstance]
instance [Mod α] : HMod α α α where
  hMod a b := Mod.mod a b

@[defaultInstance]
instance [Pow α] : HPow α α α where
  hPow a b := Pow.pow a b

@[defaultInstance]
instance [Append α] : HAppend α α α where
  hAppend a b := Append.append a b

@[defaultInstance]
instance [OrElse α] : HOrElse α α α where
  hOrElse a b := OrElse.orElse a b

@[defaultInstance]
instance [AndThen α] : HAndThen α α α where
  hAndThen a b := AndThen.andThen a b

open HAdd (hAdd)
open HMul (hMul)
open HPow (hPow)
open HAppend (hAppend)

@[reducible] def GreaterEq {α : Type u} [HasLessEq α] (a b : α) : Prop := LessEq b a
@[reducible] def Greater {α : Type u} [HasLess α] (a b : α) : Prop     := Less b a

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

instance : Add Nat where
  add := Nat.add

/- We mark the following definitions as pattern to make sure they can be used in recursive equations,
   and reduced by the equation Compiler. -/
attribute [matchPattern] Nat.add Add.add HAdd.hAdd Neg.neg

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_mul"]
protected def Nat.mul : (@& Nat) → (@& Nat) → Nat
  | a, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

instance : Mul Nat where
  mul := Nat.mul

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_pow"]
protected def Nat.pow (m : @& Nat) : (@& Nat) → Nat
  | 0      => 1
  | succ n => Nat.mul (Nat.pow m n) m

instance : Pow Nat where
  pow := Nat.pow

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_dec_eq"]
def Nat.beq : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ m => false
  | succ n, zero   => false
  | succ n, succ m => beq n m

theorem Nat.eqOfBeqEqTrue : {n m : Nat} → Eq (beq n m) true → Eq n m
  | zero,   zero,   h => rfl
  | zero,   succ m, h => Bool.noConfusion h
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have Eq (beq n m) true from h
    have Eq n m from eqOfBeqEqTrue this
    this ▸ rfl

theorem Nat.neOfBeqEqFalse : {n m : Nat} → Eq (beq n m) false → Not (Eq n m)
  | zero,   zero,   h₁, h₂ => Bool.noConfusion h₁
  | zero,   succ m, h₁, h₂ => Nat.noConfusion h₂
  | succ n, zero,   h₁, h₂ => Nat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have Eq (beq n m) false from h₁
    Nat.noConfusion h₂ (fun h₂ => absurd h₂ (neOfBeqEqFalse this))

@[extern "lean_nat_dec_eq"]
protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eqOfBeqEqTrue h)
  | false => isFalse (neOfBeqEqFalse h)

@[inline] instance : DecidableEq Nat := Nat.decEq

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_dec_le"]
def Nat.ble : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ m => true
  | succ n, zero   => false
  | succ n, succ m => ble n m

protected def Nat.le (n m : Nat) : Prop :=
  Eq (ble n m) true

instance : HasLessEq Nat where
  LessEq := Nat.le

protected def Nat.lt (n m : Nat) : Prop :=
  Nat.le (succ n) m

instance : HasLess Nat where
  Less := Nat.lt

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

set_option pp.raw true
protected theorem Nat.leTrans : {n m k : Nat} → LessEq n m → LessEq m k → LessEq n k
  | zero,   m,      k,      h₁, h₂ => zeroLe _
  | succ n, zero,   k,      h₁, h₂ => Bool.noConfusion h₁
  | succ n, succ m, zero,   h₁, h₂ => Bool.noConfusion h₂
  | succ n, succ m, succ k, h₁, h₂ =>
    have h₁' : LessEq n m from h₁
    have h₂' : LessEq m k from h₂
    show LessEq n k from
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

set_option bootstrap.genMatcherCode false in
@[extern c inline "lean_nat_sub(#1, lean_box(1))"]
def Nat.pred : Nat → Nat
  | 0      => 0
  | succ a => a

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_sub"]
protected def Nat.sub : (@& Nat) → (@& Nat) → Nat
  | a, 0      => a
  | a, succ b => pred (Nat.sub a b)

instance : Sub Nat where
  sub := Nat.sub

theorem Nat.predLePred : {n m : Nat} → LessEq n m → LessEq (pred n) (pred m)
  | zero,   zero,   h => rfl
  | zero,   succ n, h => zeroLe n
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h => h

theorem Nat.leOfSuccLeSucc {n m : Nat} : LessEq (succ n) (succ m) → LessEq n m :=
  predLePred

theorem Nat.leOfLtSucc {m n : Nat} : Less m (succ n) → LessEq m n :=
  leOfSuccLeSucc

@[extern "lean_system_platform_nbits"] constant System.Platform.getNumBits : Unit → Subtype fun (n : Nat) => Or (Eq n 32) (Eq n 64) :=
  fun _ => ⟨64, Or.inr rfl⟩ -- inhabitant

def System.Platform.numBits : Nat :=
  (getNumBits ()).val

theorem System.Platform.numBitsEq : Or (Eq numBits 32) (Eq numBits 64) :=
  (getNumBits ()).property

structure Fin (n : Nat) where
  val  : Nat
  isLt : Less val n

theorem Fin.eqOfVeq {n} : ∀ {i j : Fin n}, Eq i.val j.val → Eq i j
  | ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

theorem Fin.veqOfEq {n} {i j : Fin n} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem Fin.neOfVne {n} {i j : Fin n} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (veqOfEq h') h

instance (n : Nat) : DecidableEq (Fin n) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (Fin.eqOfVeq h)
    | isFalse h => isFalse (Fin.neOfVne h)

instance {n} : HasLess (Fin n) where
  Less a b := Less a.val b.val

instance {n} : HasLessEq (Fin n) where
  LessEq a b := LessEq a.val b.val

instance Fin.decLt {n} (a b : Fin n) :  Decidable (Less a b)  := Nat.decLt ..
instance Fin.decLe {n} (a b : Fin n) : Decidable (LessEq a b) := Nat.decLe ..

def UInt8.size : Nat := 256
structure UInt8 where
  val : Fin UInt8.size

attribute [extern "lean_uint8_of_nat"] UInt8.mk
attribute [extern "lean_uint8_to_nat"] UInt8.val

@[extern "lean_uint8_of_nat"]
def UInt8.ofNatCore (n : @& Nat) (h : Less n UInt8.size) : UInt8 := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 == #2"]
def UInt8.decEq (a b : UInt8) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt8.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt8 := UInt8.decEq

instance : Inhabited UInt8 where
  default := UInt8.ofNatCore 0 decide!

def UInt16.size : Nat := 65536
structure UInt16 where
  val : Fin UInt16.size

attribute [extern "lean_uint16_of_nat"] UInt16.mk
attribute [extern "lean_uint16_to_nat"] UInt16.val

@[extern "lean_uint16_of_nat"]
def UInt16.ofNatCore (n : @& Nat) (h : Less n UInt16.size) : UInt16 := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 == #2"]
def UInt16.decEq (a b : UInt16) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt16.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt16 := UInt16.decEq

instance : Inhabited UInt16 where
  default := UInt16.ofNatCore 0 decide!

def UInt32.size : Nat := 4294967296
structure UInt32 where
  val : Fin UInt32.size

attribute [extern "lean_uint32_of_nat"] UInt32.mk
attribute [extern "lean_uint32_to_nat"] UInt32.val

@[extern "lean_uint32_of_nat"]
def UInt32.ofNatCore (n : @& Nat) (h : Less n UInt32.size) : UInt32 := {
  val := { val := n, isLt := h }
}

@[extern "lean_uint32_to_nat"]
def UInt32.toNat (n : UInt32) : Nat := n.val.val

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 == #2"]
def UInt32.decEq (a b : UInt32) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt32.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt32 := UInt32.decEq

instance : Inhabited UInt32 where
  default := UInt32.ofNatCore 0 decide!

instance : HasLess UInt32 where
  Less a b := Less a.val b.val

instance : HasLessEq UInt32 where
  LessEq a b := LessEq a.val b.val

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 < #2"]
def UInt32.decLt (a b : UInt32) : Decidable (Less a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (Less n m))

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 <= #2"]
def UInt32.decLe (a b : UInt32) : Decidable (LessEq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (LessEq n m))

instance (a b : UInt32) : Decidable (Less a b) := UInt32.decLt a b
instance (a b : UInt32) : Decidable (LessEq a b) := UInt32.decLe a b

def UInt64.size : Nat := 18446744073709551616
structure UInt64 where
  val : Fin UInt64.size

attribute [extern "lean_uint64_of_nat"] UInt64.mk
attribute [extern "lean_uint64_to_nat"] UInt64.val

@[extern "lean_uint64_of_nat"]
def UInt64.ofNatCore (n : @& Nat) (h : Less n UInt64.size) : UInt64 := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 == #2"]
def UInt64.decEq (a b : UInt64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt64.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt64 := UInt64.decEq

instance : Inhabited UInt64 where
  default := UInt64.ofNatCore 0 decide!

def USize.size : Nat := hPow 2 System.Platform.numBits

theorem usizeSzEq : Or (Eq USize.size 4294967296) (Eq USize.size 18446744073709551616) :=
  show Or (Eq (hPow 2 System.Platform.numBits) 4294967296) (Eq (hPow 2 System.Platform.numBits) 18446744073709551616) from
  match System.Platform.numBits, System.Platform.numBitsEq with
  | _, Or.inl rfl => Or.inl (decide! : (Eq (hPow 2 32) (4294967296:Nat)))
  | _, Or.inr rfl => Or.inr (decide! : (Eq (hPow 2 64) (18446744073709551616:Nat)))

structure USize where
  val : Fin USize.size

attribute [extern "lean_usize_of_nat"] USize.mk
attribute [extern "lean_usize_to_nat"] USize.val

@[extern "lean_usize_of_nat"]
def USize.ofNatCore (n : @& Nat) (h : Less n USize.size) : USize := {
  val := { val := n, isLt := h }
}

set_option bootstrap.genMatcherCode false in
@[extern c inline "#1 == #2"]
def USize.decEq (a b : USize) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h =>isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => USize.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq USize := USize.decEq

instance : Inhabited USize where
  default := USize.ofNatCore 0 (match USize.size, usizeSzEq with
    | _, Or.inl rfl => decide!
    | _, Or.inr rfl => decide!)

@[extern "lean_usize_of_nat"]
def USize.ofNat32 (n : @& Nat) (h : Less n 4294967296) : USize := {
  val := {
    val  := n,
    isLt := match USize.size, usizeSzEq with
      | _, Or.inl rfl => h
      | _, Or.inr rfl => Nat.ltTrans h (decide! : Less 4294967296 18446744073709551616)
  }
}

abbrev Nat.isValidChar (n : Nat) : Prop :=
  Or (Less n 0xd800) (And (Less 0xdfff n) (Less n 0x110000))

abbrev UInt32.isValidChar (n : UInt32) : Prop :=
  n.toNat.isValidChar

/-- The `Char` Type represents an unicode scalar value.
    See http://www.unicode.org/glossary/#unicode_scalar_value). -/
structure Char where
  val   : UInt32
  valid : val.isValidChar

private theorem validCharIsUInt32 {n : Nat} (h : n.isValidChar) : Less n UInt32.size :=
  match h with
  | Or.inl h      => Nat.ltTrans h (decide! : Less 55296 UInt32.size)
  | Or.inr ⟨_, h⟩ => Nat.ltTrans h (decide! : Less 1114112 UInt32.size)

@[extern "lean_uint32_of_nat"]
private def Char.ofNatAux (n : Nat) (h : n.isValidChar) : Char :=
  { val := ⟨{ val := n, isLt := validCharIsUInt32 h }⟩, valid := h }

@[noinline, matchPattern]
def Char.ofNat (n : Nat) : Char :=
  dite (n.isValidChar)
    (fun h => Char.ofNatAux n h)
    (fun _ => { val := ⟨{ val := 0, isLt := decide! }⟩, valid := Or.inl decide! })

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

def Char.utf8Size (c : Char) : UInt32 :=
  let v := c.val
  ite (LessEq v (UInt32.ofNatCore 0x7F decide!))
    (UInt32.ofNatCore 1 decide!)
    (ite (LessEq v (UInt32.ofNatCore 0x7FF decide!))
      (UInt32.ofNatCore 2 decide!)
      (ite (LessEq v (UInt32.ofNatCore 0xFFFF decide!))
        (UInt32.ofNatCore 3 decide!)
        (UInt32.ofNatCore 4 decide!)))

inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α

attribute [unbox] Option

export Option (none some)

instance {α} : Inhabited (Option α) where
  default := none

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

instance {α} : Inhabited (List α) where
  default := List.nil

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

def List.set : List α → Nat → α → List α
  | cons a as, 0,          b => cons b as
  | cons a as, Nat.succ n, b => cons a (set as n b)
  | nil,       _,          _ => nil

def List.lengthAux {α : Type u} : List α → Nat → Nat
  | nil,       n => n
  | cons a as, n => lengthAux as (Nat.succ n)

def List.length {α : Type u} (as : List α) : Nat :=
  lengthAux as 0

theorem List.lengthConsEq {α} (a : α) (as : List α) : Eq (cons a as).length as.length.succ :=
  let rec aux (a : α) (as : List α) : (n : Nat) → Eq ((cons a as).lengthAux n) (as.lengthAux n).succ :=
    match as with
    | nil       => fun _ => rfl
    | cons a as => fun n => aux a as n.succ
  aux a as 0

def List.concat {α : Type u} : List α → α → List α
  | nil,       b => cons b nil
  | cons a as, b => cons a (concat as b)

def List.get {α : Type u} : (as : List α) → (i : Nat) → Less i as.length → α
  | nil,       i,          h => absurd h (Nat.notLtZero _)
  | cons a as, 0,          h => a
  | cons a as, Nat.succ i, h =>
    have Less i.succ as.length.succ from lengthConsEq .. ▸ h
    get as i (Nat.leOfSuccLeSucc this)

structure String where
  data : List Char

attribute [extern "lean_string_mk"] String.mk
attribute [extern "lean_string_data"] String.data

@[extern "lean_string_dec_eq"]
def String.decEq (s₁ s₂ : @& String) : Decidable (Eq s₁ s₂) :=
  match s₁, s₂ with
  | ⟨s₁⟩, ⟨s₂⟩ =>
   dite (Eq s₁ s₂) (fun h => isTrue (congrArg _ h)) (fun h => isFalse (fun h' => String.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq String := String.decEq

/-- A byte position in a `String`. Internally, `String`s are UTF-8 encoded.
Codepoint positions (counting the Unicode codepoints rather than bytes)
are represented by plain `Nat`s instead.
Indexing a `String` by a byte position is constant-time, while codepoint
positions need to be translated internally to byte positions in linear-time. -/
abbrev String.Pos := Nat

structure Substring where
  str : String
  startPos : String.Pos
  stopPos : String.Pos

@[inline] def Substring.bsize : Substring → Nat
  | ⟨_, b, e⟩ => e.sub b

def String.csize (c : Char) : Nat :=
  c.utf8Size.toNat

private def String.utf8ByteSizeAux : List Char → Nat → Nat
  | List.nil,       r => r
  | List.cons c cs, r => utf8ByteSizeAux cs (hAdd r (csize c))

@[extern "lean_string_utf8_byte_size"]
def String.utf8ByteSize : (@& String) → Nat
  | ⟨s⟩ => utf8ByteSizeAux s 0

@[inline] def String.bsize (s : String) : Nat :=
  utf8ByteSize s

@[inline] def String.toSubstring (s : String) : Substring := {
  str := s,
  startPos := 0,
  stopPos  := s.bsize
}

@[extern c inline "#3"]
unsafe def unsafeCast {α : Type u} {β : Type v} (a : α) : β :=
  cast lcProof (PUnit.{v})

@[neverExtract, extern "lean_panic_fn"]
constant panic {α : Type u} [Inhabited α] (msg : String) : α

/-
The Compiler has special support for arrays.
They are implemented using dynamic arrays: https://en.wikipedia.org/wiki/Dynamic_array
-/
structure Array (α : Type u) where
  data : List α

attribute [extern "lean_array_data"] Array.data
attribute [extern "lean_array_mk"] Array.mk

/- The parameter `c` is the initial capacity -/
@[extern "lean_mk_empty_array_with_capacity"]
def Array.mkEmpty {α : Type u} (c : @& Nat) : Array α := {
  data := List.nil
}

def Array.empty {α : Type u} : Array α :=
  mkEmpty 0

@[reducible, extern "lean_array_get_size"]
def Array.size {α : Type u} (a : @& Array α) : Nat :=
 a.data.length

@[extern "lean_array_fget"]
def Array.get {α : Type u} (a : @& Array α) (i : @& Fin a.size) : α :=
  a.data.get i.val i.isLt

@[inline] def Array.getD (a : Array α) (i : Nat) (v₀ : α) : α :=
  dite (Less i a.size) (fun h => a.get ⟨i, h⟩) (fun _ => v₀)

/- "Comfortable" version of `fget`. It performs a bound check at runtime. -/
@[extern "lean_array_get"]
def Array.get! {α : Type u} [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
  Array.getD a i arbitrary

def Array.getOp {α : Type u} [Inhabited α] (self : Array α) (idx : Nat) : α :=
  self.get! idx

@[extern "lean_array_push"]
def Array.push {α : Type u} (a : Array α) (v : α) : Array α := {
  data := List.concat a.data v
}

@[extern "lean_array_fset"]
def Array.set (a : Array α) (i : @& Fin a.size) (v : α) : Array α := {
  data := a.data.set i.val v
}

@[inline] def Array.setD (a : Array α) (i : Nat) (v : α) : Array α :=
  dite (Less i a.size) (fun h => a.set ⟨i, h⟩ v) (fun _ => a)

@[extern "lean_array_set"]
def Array.set! (a : Array α) (i : @& Nat) (v : α) : Array α :=
  Array.setD a i v

-- Slower `Array.append` used in quotations.
protected def Array.appendCore {α : Type u}  (as : Array α) (bs : Array α) : Array α :=
  let rec loop (i : Nat) (j : Nat) (as : Array α) : Array α :=
    dite (Less j bs.size)
      (fun hlt =>
        match i with
        | 0           => as
        | Nat.succ i' => loop i' (hAdd j 1) (as.push (bs.get ⟨j, hlt⟩)))
      (fun _ => as)
  loop bs.size 0 as

class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

export Bind (bind)

class Pure (f : Type u → Type v) where
  pure {α : Type u} : α → f α

export Pure (pure)

class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map      : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)

class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq  : {α β : Type u} → f (α → β) → f α → f β

class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α : Type u} → f α → f PUnit → f α

class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {β : Type u} → f PUnit → f β → f β

class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      := fun f x => bind x (Function.comp pure f)
  seq      := fun f x => bind f fun y => Functor.map y x
  seqLeft  := fun x y => bind x fun a => bind y (fun _ => pure a)
  seqRight := fun x y => bind x fun _ => y

instance {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) where
  default := pure

instance {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) where
  default := pure arbitrary

-- A fusion of Haskell's `sequence` and `map`
def Array.sequenceMap {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (f : α → m β) : m (Array β) :=
  let rec loop (i : Nat) (j : Nat) (bs : Array β) : m (Array β) :=
    dite (Less j as.size)
      (fun hlt =>
        match i with
        | 0           => pure bs
        | Nat.succ i' => Bind.bind (f (as.get ⟨j, hlt⟩)) fun b => loop i' (hAdd j 1) (bs.push b))
      (fun _ => bs)
  loop as.size 0 Array.empty

/-- A Function for lifting a computation from an inner Monad to an outer Monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α

/-- The reflexive-transitive closure of `MonadLift`.
    `monadLift` is used to transitively lift monadic computations such as `StateT.get` or `StateT.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α

export MonadLiftT (monadLift)

abbrev liftM := @monadLift

instance (m n o) [MonadLift n o] [MonadLiftT m n] : MonadLiftT m o where
  monadLift x := MonadLift.monadLift (m := n) (monadLift x)

instance (m) : MonadLiftT m m where
  monadLift x := x

/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor). -/
class MonadFunctor (m : Type u → Type v) (n : Type u → Type w) where
  monadMap {α : Type u} : (∀ {β}, m β → m β) → n α → n α

/-- The reflexive-transitive closure of `MonadFunctor`.
    `monadMap` is used to transitively lift Monad morphisms -/
class MonadFunctorT (m : Type u → Type v) (n : Type u → Type w) where
  monadMap {α : Type u} : (∀ {β}, m β → m β) → n α → n α

export MonadFunctorT (monadMap)

instance (m n o) [MonadFunctor n o] [MonadFunctorT m n] : MonadFunctorT m o where
  monadMap f := MonadFunctor.monadMap (m := n) (monadMap (m := m) f)

instance monadFunctorRefl (m) : MonadFunctorT m m where
  monadMap f := f

inductive Except (ε : Type u) (α : Type v) where
  | error : ε → Except ε α
  | ok    : α → Except ε α

attribute [unbox] Except

instance {ε : Type u} {α : Type v} [Inhabited ε] : Inhabited (Except ε α) where
  default := Except.error arbitrary

/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class MonadExceptOf (ε : Type u) (m : Type v → Type w) where
  throw {α : Type v} : ε → m α
  tryCatch {α : Type v} : m α → (ε → m α) → m α

abbrev throwThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (e : ε) : m α :=
  MonadExceptOf.throw e

abbrev tryCatchThe (ε : Type u) {m : Type v → Type w} [MonadExceptOf ε m] {α : Type v} (x : m α) (handle : ε → m α) : m α :=
  MonadExceptOf.tryCatch x handle

/-- Similar to `MonadExceptOf`, but `ε` is an outParam for convenience -/
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw {α : Type v} : ε → m α
  tryCatch {α : Type v} : m α → (ε → m α) → m α

export MonadExcept (throw tryCatch)

instance (ε : outParam (Type u)) (m : Type v → Type w) [MonadExceptOf ε m] : MonadExcept ε m where
  throw    := throwThe ε
  tryCatch := tryCatchThe ε

namespace MonadExcept
variable {ε : Type u} {m : Type v → Type w}

@[inline] protected def orelse [MonadExcept ε m] {α : Type v} (t₁ t₂ : m α) : m α :=
  tryCatch t₁ fun _ => t₂

instance [MonadExcept ε m] {α : Type v} : OrElse (m α) where
  orElse := MonadExcept.orelse

end MonadExcept

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α

instance (ρ : Type u) (m : Type u → Type v) (α : Type u) [Inhabited (m α)] : Inhabited (ReaderT ρ m α) where
  default := fun _ => arbitrary

@[inline] def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

@[reducible] def Reader (ρ : Type u) := ReaderT ρ id

namespace ReaderT

section
variable {ρ : Type u} {m : Type u → Type v} {α : Type u}

instance  : MonadLift m (ReaderT ρ m) where
  monadLift x := fun _ => x

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ReaderT ρ m) where
  throw e  := liftM (m := m) (throw e)
  tryCatch := fun x c r => tryCatchThe ε (x r) (fun e => (c e) r)

end

section
variable {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

@[inline] protected def read : ReaderT ρ m ρ :=
  pure

@[inline] protected def pure (a : α) : ReaderT ρ m α :=
  fun r => pure a

@[inline] protected def bind (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) : ReaderT ρ m β :=
  fun r => bind (x r) fun a => f a r

@[inline] protected def map (f : α → β) (x : ReaderT ρ m α) : ReaderT ρ m β :=
  fun r => Functor.map f (x r)

instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
  map  := ReaderT.map

instance (ρ m) [Monad m] : MonadFunctor m (ReaderT ρ m) where
  monadMap f x := fun ctx => f (x ctx)

@[inline] protected def adapt {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α :=
  fun x r => x (f r)

end
end ReaderT

/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this Function cannot be lifted using `monadLift`.
    Instead, the `MonadReaderAdapter` class provides the more general `adaptReader` Function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadReader (ρ : outParam (Type u)) (n : Type u → Type u) where
      lift {α : Type u} : (∀ {m : Type u → Type u} [Monad m], ReaderT ρ m α) → n α
    ```
    -/
class MonadReaderOf (ρ : Type u) (m : Type u → Type v) where
  read : m ρ

@[inline] def readThe (ρ : Type u) {m : Type u → Type v} [MonadReaderOf ρ m] : m ρ :=
  MonadReaderOf.read

/-- Similar to `MonadReaderOf`, but `ρ` is an outParam for convenience -/
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  read : m ρ

export MonadReader (read)

instance (ρ : Type u) (m : Type u → Type v) [MonadReaderOf ρ m] : MonadReader ρ m where
  read := readThe ρ

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [MonadReaderOf ρ m] : MonadReaderOf ρ n where
  read := liftM (m := m) read

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadReaderOf ρ (ReaderT ρ m) where
  read := ReaderT.read

class MonadWithReaderOf (ρ : Type u) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α

@[inline] def withTheReader (ρ : Type u) {m : Type u → Type v} [MonadWithReaderOf ρ m] {α : Type u} (f : ρ → ρ) (x : m α) : m α :=
  MonadWithReaderOf.withReader f x

class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α

export MonadWithReader (withReader)

instance (ρ : Type u) (m : Type u → Type v) [MonadWithReaderOf ρ m] : MonadWithReader ρ m where
  withReader := withTheReader ρ

instance {ρ : Type u} {m : Type u → Type v} {n : Type u → Type v} [MonadFunctor m n] [MonadWithReaderOf ρ m] : MonadWithReaderOf ρ n where
  withReader f := monadMap (m := m) (withTheReader ρ f)

instance {ρ : Type u} {m : Type u → Type v} [Monad m] : MonadWithReaderOf ρ (ReaderT ρ m) where
  withReader f x := fun ctx => x (f ctx)

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class MonadStateOf (σ : Type u) (m : Type u → Type v) where
  /- Obtain the top-most State of a Monad stack. -/
  get : m σ
  /- Set the top-most State of a Monad stack. -/
  set : σ → m PUnit
  /- Map the top-most State of a Monad stack.

     Note: `modifyGet f` may be preferable to `do s <- get; let (a, s) := f s; put s; pure a`
     because the latter does not use the State linearly (without sufficient inlining). -/
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

export MonadStateOf (set)

abbrev getThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] : m σ :=
  MonadStateOf.get

@[inline] abbrev modifyThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → σ) : m PUnit :=
  MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

@[inline] abbrev modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → Prod α σ) : m α :=
  MonadStateOf.modifyGet f

/-- Similar to `MonadStateOf`, but `σ` is an outParam for convenience -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) where
  get : m σ
  set : σ → m PUnit
  modifyGet {α : Type u} : (σ → Prod α σ) → m α

export MonadState (get modifyGet)

instance (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m where
  set       := MonadStateOf.set
  get       := getThe σ
  modifyGet := fun f => MonadStateOf.modifyGet f

@[inline] def modify {σ : Type u} {m : Type u → Type v} [MonadState σ m] (f : σ → σ) : m PUnit :=
  modifyGet fun s => (PUnit.unit, f s)

@[inline] def getModify {σ : Type u} {m : Type u → Type v} [MonadState σ m] [Monad m] (f : σ → σ) : m σ :=
  modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [MonadLift m n] [MonadStateOf σ m] : MonadStateOf σ n where
  get       := liftM (m := m) MonadStateOf.get
  set       := fun s => liftM (m := m) (MonadStateOf.set s)
  modifyGet := fun f => monadLift (m := m) (MonadState.modifyGet f)

namespace EStateM

inductive Result (ε σ α : Type u) where
  | ok    : α → σ → Result ε σ α
  | error : ε → σ → Result ε σ α

variable {ε σ α : Type u}

instance [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) where
  default := Result.error arbitrary arbitrary

end EStateM

open EStateM (Result) in
def EStateM (ε σ α : Type u) := σ → Result ε σ α

namespace EStateM

variable {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (EStateM ε σ α) where
  default := fun s => Result.error arbitrary s

@[inline] protected def pure (a : α) : EStateM ε σ α := fun s =>
  Result.ok a s

@[inline] protected def set (s : σ) : EStateM ε σ PUnit := fun _ =>
  Result.ok ⟨⟩ s

@[inline] protected def get : EStateM ε σ σ := fun s =>
  Result.ok s s

@[inline] protected def modifyGet (f : σ → Prod α σ) : EStateM ε σ α := fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : EStateM ε σ α := fun s =>
  Result.error e s

/-- Auxiliary instance for saving/restoring the "backtrackable" part of the state. -/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) where
  save    : σ → δ
  restore : σ → δ → σ

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

instance : Monad (EStateM ε σ) where
  bind     := EStateM.bind
  pure     := EStateM.pure
  map      := EStateM.map
  seqRight := EStateM.seqRight

instance {δ} [Backtrackable δ σ] : OrElse (EStateM ε σ α) where
  orElse := EStateM.orElse

instance : MonadStateOf σ (EStateM ε σ) where
  set       := EStateM.set
  get       := EStateM.get
  modifyGet := EStateM.modifyGet

instance {δ} [Backtrackable δ σ] : MonadExceptOf ε (EStateM ε σ) where
  throw    := EStateM.throw
  tryCatch := EStateM.tryCatch

@[inline] def run (x : EStateM ε σ α) (s : σ) : Result ε σ α :=
  x s

@[inline] def run' (x : EStateM ε σ α) (s : σ) : Option α :=
  match run x s with
  | Result.ok v _    => some v
  | Result.error _ _ => none

@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ where
  save    := dummySave
  restore := dummyRestore

end EStateM

class Hashable (α : Type u) where
  hash : α → USize

export Hashable (hash)

@[extern "lean_usize_mix_hash"]
constant mixHash (u₁ u₂ : USize) : USize

@[extern "lean_string_hash"]
protected constant String.hash (s : @& String) : USize

instance : Hashable String where
  hash := String.hash

namespace Lean

/- Hierarchical names -/
inductive Name where
  | anonymous : Name
  | str : Name → String → USize → Name
  | num : Name → Nat → USize → Name

instance : Inhabited Name where
  default := Name.anonymous

protected def Name.hash : Name → USize
  | Name.anonymous => USize.ofNat32 1723 decide!
  | Name.str p s h => h
  | Name.num p v h => h

instance : Hashable Name where
  hash := Name.hash

namespace Name

@[export lean_name_mk_string]
def mkStr (p : Name) (s : String) : Name :=
  Name.str p s (mixHash (hash p) (hash s))

@[export lean_name_mk_numeral]
def mkNum (p : Name) (v : Nat) : Name :=
  Name.num p v (mixHash (hash p) (dite (Less v USize.size) (fun h => USize.ofNatCore v h) (fun _ => USize.ofNat32 17 decide!)))

def mkSimple (s : String) : Name :=
  mkStr Name.anonymous s

@[extern "lean_name_eq"]
protected def beq : (@& Name) → (@& Name) → Bool
  | anonymous,   anonymous   => true
  | str p₁ s₁ _, str p₂ s₂ _ => and (BEq.beq s₁ s₂) (Name.beq p₁ p₂)
  | num p₁ n₁ _, num p₂ n₂ _ => and (BEq.beq n₁ n₂) (Name.beq p₁ p₂)
  | _,           _           => false

instance : BEq Name where
  beq := Name.beq

protected def append : Name → Name → Name
  | n, anonymous => n
  | n, str p s _ => Name.mkStr (Name.append n p) s
  | n, num p d _ => Name.mkNum (Name.append n p) d

instance : Append Name where
  append := Name.append

end Name

/- Syntax -/

/-- Source information of tokens. -/
inductive SourceInfo where
  /-
    Token from original input with whitespace and position information.
    `leading` will be inferred after parsing by `Syntax.updateLeading`. During parsing,
    it is not at all clear what the preceding token was, especially with backtracking. -/
  | original (leading : Substring) (pos : String.Pos) (trailing : Substring)
  /-
    Synthesized token (e.g. from a quotation) annotated with a span from the original source.
    In the delaborator, we "misuse" this constructor to store synthetic positions identifying
    subterms. -/
  | synthetic (pos : String.Pos) (endPos : String.Pos)
  /- Synthesized token without position information. -/
  | protected none

instance : Inhabited SourceInfo := ⟨SourceInfo.none⟩

namespace SourceInfo

def getPos? (info : SourceInfo) (originalOnly := false) : Option String.Pos :=
  match info, originalOnly with
  | original (pos := pos) ..,  _     => some pos
  | synthetic (pos := pos) .., false => some pos
  | _,                         _     => none

end SourceInfo

abbrev SyntaxNodeKind := Name

/- Syntax AST -/

inductive Syntax where
  | missing : Syntax
  | node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom   (info : SourceInfo) (val : String) : Syntax
  | ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Prod Name (List String))) : Syntax

instance : Inhabited Syntax where
  default := Syntax.missing

/- Builtin kinds -/
def choiceKind : SyntaxNodeKind := `choice
def nullKind : SyntaxNodeKind := `null
def identKind : SyntaxNodeKind := `ident
def strLitKind : SyntaxNodeKind := `strLit
def charLitKind : SyntaxNodeKind := `charLit
def numLitKind : SyntaxNodeKind := `numLit
def scientificLitKind : SyntaxNodeKind := `scientificLit
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
  | Syntax.atom _ v      => Name.mkSimple v
  | Syntax.ident _ _ _ _ => identKind

def setKind (stx : Syntax) (k : SyntaxNodeKind) : Syntax :=
  match stx with
  | Syntax.node _ args => Syntax.node k args
  | _                  => stx

def isOfKind (stx : Syntax) (k : SyntaxNodeKind) : Bool :=
  beq stx.getKind k

def getArg (stx : Syntax) (i : Nat) : Syntax :=
  match stx with
  | Syntax.node _ args => args.getD i Syntax.missing
  | _                  => Syntax.missing

-- Add `stx[i]` as sugar for `stx.getArg i`
@[inline] def getOp (self : Syntax) (idx : Nat) : Syntax :=
  self.getArg idx

def getArgs (stx : Syntax) : Array Syntax :=
  match stx with
  | Syntax.node _ args => args
  | _                  => Array.empty

def getNumArgs (stx : Syntax) : Nat :=
  match stx with
  | Syntax.node _ args => args.size
  | _                  => 0

def setArgs (stx : Syntax) (args : Array Syntax) : Syntax :=
  match stx with
  | node k _ => node k args
  | stx      => stx

def setArg (stx : Syntax) (i : Nat) (arg : Syntax) : Syntax :=
  match stx with
  | node k args => node k (args.setD i arg)
  | stx         => stx

/-- Retrieve the left-most leaf's info in the Syntax tree. -/
partial def getHeadInfo? : Syntax → Option SourceInfo
  | atom info _      => some info
  | ident info _ _ _ => some info
  | node _ args      =>
    let rec loop (i : Nat) : Option SourceInfo :=
      match decide (Less i args.size) with
      | true => match getHeadInfo? (args.get! i) with
         | some info => some info
         | none      => loop (hAdd i 1)
      | false => none
    loop 0
  | _                => none

/-- Retrieve the left-most leaf's info in the Syntax tree, or `none` if there is no token. -/
partial def getHeadInfo (stx : Syntax) : SourceInfo :=
  match stx.getHeadInfo? with
  | some info => info
  | none      => SourceInfo.none

def getPos? (stx : Syntax) (originalOnly := false) : Option String.Pos :=
  stx.getHeadInfo.getPos? originalOnly

partial def getTailPos? (stx : Syntax) (originalOnly := false) : Option String.Pos :=
  match stx, originalOnly with
  | atom (SourceInfo.original (pos := pos) ..) val,    _      => some (pos.add val.bsize)
  | atom (SourceInfo.synthetic (endPos := pos) ..) _,  false  => some pos
  | ident (SourceInfo.original (pos := pos) ..) val .., _     => some (pos.add val.bsize)
  | ident (SourceInfo.synthetic (endPos := pos) ..) .., false => some pos
  | node _ args,                                        _     =>
    let rec loop (i : Nat) : Option String.Pos :=
      match decide (Less i args.size) with
      | true => match getTailPos? (args.get! ((args.size.sub i).sub 1)) with
         | some info => some info
         | none      => loop (hAdd i 1)
      | false => none
    loop 0
  | _, _ => none

/--
  An array of syntax elements interspersed with separators. Can be coerced to/from `Array Syntax` to automatically
  remove/insert the separators. -/
structure SepArray (sep : String) where
  elemsAndSeps : Array Syntax

end Syntax

def SourceInfo.fromRef (ref : Syntax) : SourceInfo :=
  match ref.getPos?, ref.getTailPos? with
  | some pos, some tailPos => SourceInfo.synthetic pos tailPos
  | _,        _            => SourceInfo.none

def mkAtomFrom (src : Syntax) (val : String) : Syntax :=
  Syntax.atom src.getHeadInfo val

/- Parser descriptions -/

inductive ParserDescr where
  | const  (name : Name)
  | unary  (name : Name) (p : ParserDescr)
  | binary (name : Name) (p₁ p₂ : ParserDescr)
  | node (kind : SyntaxNodeKind) (prec : Nat) (p : ParserDescr)
  | trailingNode (kind : SyntaxNodeKind) (prec : Nat) (p : ParserDescr)
  | symbol (val : String)
  | nonReservedSymbol (val : String) (includeIdent : Bool)
  | cat (catName : Name) (rbp : Nat)
  | parser (declName : Name)
  | nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : ParserDescr)
  | sepBy  (p : ParserDescr) (sep : String) (psep : ParserDescr) (allowTrailingSep : Bool := false)
  | sepBy1 (p : ParserDescr) (sep : String) (psep : ParserDescr) (allowTrailingSep : Bool := false)

instance : Inhabited ParserDescr where
  default := ParserDescr.symbol ""

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
def firstFrontendMacroScope := hAdd reservedMacroScope 1

class MonadRef (m : Type → Type) where
  getRef      : m Syntax
  withRef {α} : Syntax → m α → m α

export MonadRef (getRef)

instance (m n : Type → Type) [MonadLift m n] [MonadFunctor m n] [MonadRef m] : MonadRef n where
  getRef  := liftM (getRef : m _)
  withRef := fun ref x => monadMap (m := m) (MonadRef.withRef ref) x

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
  match ref.getPos? with
  | some _ => ref
  | _      => oldRef

@[inline] def withRef {m : Type → Type} [Monad m] [MonadRef m] {α} (ref : Syntax) (x : m α) : m α :=
  bind getRef fun oldRef =>
  let ref := replaceRef ref oldRef
  MonadRef.withRef ref x

/-- A monad that supports syntax quotations. Syntax quotations (in term
    position) are monadic values that when executed retrieve the current "macro
    scope" from the monad and apply it to every identifier they introduce
    (independent of whether this identifier turns out to be a reference to an
    existing declaration, or an actually fresh binding during further
    elaboration). We also apply the position of the result of `getRef` to each
    introduced symbol, which results in better error positions than not applying
    any position. -/
class MonadQuotation (m : Type → Type) extends MonadRef m where
  -- Get the fresh scope of the current macro invocation
  getCurrMacroScope : m MacroScope
  getMainModule     : m Name
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
  withFreshMacroScope {α : Type} : m α → m α

export MonadQuotation (getCurrMacroScope getMainModule withFreshMacroScope)

def MonadRef.mkInfoFromRefPos [Monad m] [MonadRef m] : m SourceInfo := do
  SourceInfo.fromRef (← getRef)

instance {m n : Type → Type} [MonadFunctor m n] [MonadLift m n] [MonadQuotation m] : MonadQuotation n where
  getCurrMacroScope   := liftM (m := m) getCurrMacroScope
  getMainModule       := liftM (m := m) getMainModule
  withFreshMacroScope := monadMap (m := m) withFreshMacroScope

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
  | Name.str p s _   => match beq s "_@" with
    | true  => p
    | false => eraseMacroScopesAux p
  | Name.num p _ _   => eraseMacroScopesAux p
  | Name.anonymous   => Name.anonymous

@[export lean_erase_macro_scopes]
def Name.eraseMacroScopes (n : Name) : Name :=
  match n.hasMacroScopes with
  | true  => eraseMacroScopesAux n
  | false => n

private def simpMacroScopesAux : Name → Name
  | Name.num p i _ => Name.mkNum (simpMacroScopesAux p) i
  | n              => eraseMacroScopesAux n

/- Helper function we use to create binder names that do not need to be unique. -/
@[export lean_simp_macro_scopes]
def Name.simpMacroScopes (n : Name) : Name :=
  match n.hasMacroScopes with
  | true  => simpMacroScopesAux n
  | false => n

structure MacroScopesView where
  name       : Name
  imported   : Name
  mainModule : Name
  scopes     : List MacroScope

instance : Inhabited MacroScopesView where
  default := ⟨arbitrary, arbitrary, arbitrary, arbitrary⟩

def MacroScopesView.review (view : MacroScopesView) : Name :=
  match view.scopes with
  | List.nil      => view.name
  | List.cons _ _ =>
    let base := (Name.mkStr (hAppend (hAppend (Name.mkStr view.name "_@") view.imported) view.mainModule) "_hyg")
    view.scopes.foldl Name.mkNum base

private def assembleParts : List Name → Name → Name
  | List.nil,                      acc => acc
  | List.cons (Name.str _ s _) ps, acc => assembleParts ps (Name.mkStr acc s)
  | List.cons (Name.num _ n _) ps, acc => assembleParts ps (Name.mkNum acc n)
  | _,                             acc => panic "Error: unreachable @ assembleParts"

private def extractImported (scps : List MacroScope) (mainModule : Name) : Name → List Name → MacroScopesView
  | n@(Name.str p str _), parts =>
    match beq str "_@" with
    | true  => { name := p, mainModule := mainModule, imported := assembleParts parts Name.anonymous, scopes := scps }
    | false => extractImported scps mainModule p (List.cons n parts)
  | n@(Name.num p str _), parts => extractImported scps mainModule p (List.cons n parts)
  | _,                    _     => panic "Error: unreachable @ extractImported"

private def extractMainModule (scps : List MacroScope) : Name → List Name → MacroScopesView
  | n@(Name.str p str _), parts =>
    match beq str "_@" with
    | true  => { name := p, mainModule := assembleParts parts Name.anonymous, imported := Name.anonymous, scopes := scps }
    | false => extractMainModule scps p (List.cons n parts)
  | n@(Name.num p num _), acc => extractImported scps (assembleParts acc Name.anonymous) n List.nil
  | _,                    _   => panic "Error: unreachable @ extractMainModule"

private def extractMacroScopesAux : Name → List MacroScope → MacroScopesView
  | Name.num p scp _, acc => extractMacroScopesAux p (List.cons scp acc)
  | Name.str p str _, acc => extractMainModule acc p List.nil -- str must be "_hyg"
  | _,                _   => panic "Error: unreachable @ extractMacroScopesAux"

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
    | true  => Name.mkNum n scp
    | false =>
      { view with
        imported   := view.scopes.foldl Name.mkNum (hAppend view.imported view.mainModule),
        mainModule := mainModule,
        scopes     := List.cons scp List.nil
      }.review
  | false =>
    Name.mkNum (Name.mkStr (hAppend (Name.mkStr n "_@") mainModule) "_hyg") scp

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
instance : Inhabited MacroEnv where
  default := MacroEnvPointed.val

structure Context where
  macroEnv       : MacroEnv
  mainModule     : Name
  currMacroScope : MacroScope
  currRecDepth   : Nat := 0
  maxRecDepth    : Nat := defaultMaxRecDepth
  ref            : Syntax

inductive Exception where
  | error             : Syntax → String → Exception
  | unsupportedSyntax : Exception

end Macro

abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception MacroScope)

abbrev Macro := Syntax → MacroM Syntax

namespace Macro

instance : MonadRef MacroM where
  getRef     := bind read fun ctx => pure ctx.ref
  withRef    := fun ref x => withReader (fun ctx => { ctx with ref := ref }) x

def addMacroScope (n : Name) : MacroM Name :=
  bind read fun ctx =>
  pure (Lean.addMacroScope ctx.mainModule n ctx.currMacroScope)

def throwUnsupported {α} : MacroM α :=
  throw Exception.unsupportedSyntax

def throwError {α} (msg : String) : MacroM α :=
  bind getRef fun ref =>
  throw (Exception.error ref msg)

def throwErrorAt {α} (ref : Syntax) (msg : String) : MacroM α :=
  withRef ref (throwError msg)

@[inline] protected def withFreshMacroScope {α} (x : MacroM α) : MacroM α :=
  bind (modifyGet (fun s => (s, hAdd s 1))) fun fresh =>
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : MacroM α) : MacroM α :=
  bind read fun ctx =>
  match beq ctx.currRecDepth ctx.maxRecDepth with
  | true  => throw (Exception.error ref maxRecDepthErrorMessage)
  | false => withReader (fun ctx => { ctx with currRecDepth := hAdd ctx.currRecDepth 1 }) x

instance : MonadQuotation MacroM where
  getCurrMacroScope   := fun ctx => pure ctx.currMacroScope
  getMainModule       := fun ctx => pure ctx.mainModule
  withFreshMacroScope := Macro.withFreshMacroScope

unsafe def mkMacroEnvImp (expandMacro? : Syntax → MacroM (Option Syntax)) : MacroEnv :=
  unsafeCast expandMacro?

@[implementedBy mkMacroEnvImp]
constant mkMacroEnv (expandMacro? : Syntax → MacroM (Option Syntax)) : MacroEnv

def expandMacroNotAvailable? (stx : Syntax) : MacroM (Option Syntax) :=
  throwErrorAt stx "expandMacro has not been set"

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

namespace PrettyPrinter

abbrev UnexpandM := EStateM Unit Unit

/--
  Function that tries to reverse macro expansions as a post-processing step of delaboration.
  While less general than an arbitrary delaborator, it can be declared without importing `Lean`.
  Used by the `[appUnexpander]` attribute. -/
-- a `kindUnexpander` could reasonably be added later
abbrev Unexpander := Syntax → UnexpandM Syntax

-- unexpanders should not need to introduce new names
instance : MonadQuotation UnexpandM where
  getRef              := pure Syntax.missing
  withRef             := fun _ => id
  getCurrMacroScope   := pure 0
  getMainModule       := pure `_fakeMod
  withFreshMacroScope := id

end PrettyPrinter

end Lean

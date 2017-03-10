/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude

notation `Prop` := Sort 0

/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` == `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50
reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- types and type constructors -/

reserve infixr ` ⊕ `:30
reserve infixr ` × `:35

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infix ` ^ `:80

reserve infixr ` ∘ `:90                 -- input with \comp

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65

/- set operations -/

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50
reserve infix ` ⊂ `:50
reserve infix ` ⊃ `:50
reserve infix ` \ `:70

/- other symbols -/

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:67
reserve infixl `; `:1

universes u v w

/-- Gadget for optional parameter support. -/
@[reducible] def opt_param (α : Sort u) (default : α) : Sort u :=
α

/-- Gadget for marking output parameters in type classes. -/
@[reducible] def out_param (α : Sort u) : Sort u := α

inductive punit : Sort u
| star : punit

inductive unit : Type
| star : unit

/--
Gadget for defining thunks, thunk parameters have special treatment.
Example: given
      def f (s : string) (t : thunk nat) : nat
an application
     f "hello" 10
 is converted into
     f "hello" (λ _, 10)
-/
@[reducible] def thunk (α : Type u) : Type u :=
unit → α

inductive true : Prop
| intro : true

inductive false : Prop

inductive empty : Type

def not (a : Prop) := a → false
prefix `¬` := not

inductive eq {α : Sort u} (a : α) : α → Prop
| refl : eq a

init_quotient

inductive heq {α : Sort u} (a : α) : Π {β : Sort u}, β → Prop
| refl : heq a

structure prod (α : Type u) (β : Type v) :=
(fst : α) (snd : β)

/- Similar to prod, but α and β can be propositions.
   We use this type internally to automatically generate the brec_on recursor. -/
structure pprod (α : Sort u) (β : Sort v) :=
(fst : α) (snd : β)

inductive and (a b : Prop) : Prop
| intro : a → b → and

def and.elim_left {a b : Prop} (h : and a b) : a :=
and.rec (λ ha hb, ha) h

def and.left := @and.elim_left

def and.elim_right {a b : Prop} (h : and a b) : b :=
and.rec (λ ha hb, hb) h

def and.right := @and.elim_right

/- eq basic support -/

infix = := eq

attribute [refl] eq.refl

@[pattern] def rfl {α : Sort u} {a : α} : a = a := eq.refl a

@[elab_as_eliminator, subst]
lemma eq.subst {α : Sort u} {P : α → Prop} {a b : α} (h₁ : a = b) (h₂ : P a) : P b :=
eq.rec h₂ h₁

notation h1 ▸ h2 := eq.subst h1 h2

@[trans] lemma eq.trans {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
h₂ ▸ h₁

@[symm] lemma eq.symm {α : Sort u} {a b : α} (h : a = b) : b = a :=
h ▸ rfl

infix == := heq

lemma eq_of_heq {α : Sort u} {a a' : α} (h : a == a') : a = a' :=
have ∀ (α' : Sort u) (a' : α') (h₁ : @heq α a α' a') (h₂ : α = α'), (eq.rec_on h₂ a : α') = a', from
  λ (α' : Sort u) (a' : α') (h₁ : @heq α a α' a'), heq.rec_on h₁ (λ h₂ : α = α, rfl),
show (eq.rec_on (eq.refl α) a : α) = a', from
  this α a' h (eq.refl α)

-- The following four lemmas could not be automatically generated when the
-- structures were declared, so we prove them manually here.
lemma prod.mk.inj {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  : (x₁, y₁) = (x₂, y₂) → and (x₁ = x₂) (y₁ = y₂) :=
assume (H_eq : (x₁, y₁) = (x₂, y₂)),
have H_nc : (x₁ = x₂ → y₁ = y₂ → and (x₁ = x₂) (y₁ = y₂)) → and (x₁ = x₂) (y₁ = y₂), from
  @prod.no_confusion _ _ (and (x₁ = x₂) (y₁ = y₂)) _ _ H_eq,
H_nc (assume Hx Hy, and.intro Hx Hy)

lemma prod.mk.inj_arrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  : (x₁, y₁) = (x₂, y₂) → Π ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
assume H_eq P,
@prod.no_confusion _ _ P _ _ H_eq

lemma pprod.mk.inj {α : Sort u} {β : Sort v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  : pprod.mk x₁ y₁ = pprod.mk x₂ y₂ → and (x₁ = x₂) (y₁ = y₂) :=
assume (H_eq : pprod.mk x₁ y₁ = pprod.mk x₂ y₂),
have H_nc : (x₁ = x₂ → y₁ = y₂ → and (x₁ = x₂) (y₁ = y₂)) → and (x₁ = x₂) (y₁ = y₂), from
  @pprod.no_confusion _ _ (and (x₁ = x₂) (y₁ = y₂)) _ _ H_eq,
H_nc (assume Hx Hy, and.intro Hx Hy)

lemma pprod.mk.inj_arrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  : (x₁, y₁) = (x₂, y₂) → Π ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
assume H_eq P,
@prod.no_confusion _ _ P _ _ H_eq

inductive sum (α : Type u) (β : Type v)
| inl {} : α → sum
| inr {} : β → sum

inductive psum (α : Sort u) (β : Sort v)
| inl {} : α → psum
| inr {} : β → psum

inductive or (a b : Prop) : Prop
| inl {} : a → or
| inr {} : b → or

def or.intro_left {a : Prop} (b : Prop) (ha : a) : or a b :=
or.inl ha

def or.intro_right (a : Prop) {b : Prop} (hb : b) : or a b :=
or.inr hb

structure sigma {α : Type u} (β : α → Type v) :=
mk :: (fst : α) (snd : β fst)

structure psigma {α : Sort u} (β : α → Sort v) :=
mk :: (fst : α) (snd : β fst)

inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

namespace pos_num
  def succ : pos_num → pos_num
  | one      := bit0 one
  | (bit1 n) := bit0 (succ n)
  | (bit0 n) := bit1 n
end pos_num

inductive num : Type
| zero  : num
| pos   : pos_num → num

namespace num
  open pos_num
  def succ : num → num
  | zero    := pos one
  | (pos p) := pos (pos_num.succ p)
end num

inductive bool : Type
| ff : bool
| tt : bool

/- Remark: subtype must take a Sort instead of Type because of the axiom strong_indefinite_description. -/
structure subtype {α : Sort u} (p : α → Prop) :=
(val : α) (property : p val)

attribute [pp_using_anonymous_constructor] sigma psigma subtype pprod

class inductive decidable (p : Prop)
| is_false : ¬p → decidable
| is_true :  p → decidable

@[reducible]
def decidable_pred {α : Sort u} (r : α → Prop) :=
Π (a : α), decidable (r a)

@[reducible]
def decidable_rel {α : Sort u} (r : α → α → Prop) :=
Π (a b : α), decidable (r a b)

@[reducible]
def decidable_eq (α : Sort u) :=
decidable_rel (@eq α)

inductive option (α : Type u)
| none {} : option
| some    : α → option

export option (none some)
export bool (ff tt)

inductive list (T : Type u)
| nil {} : list
| cons   : T → list → list

inductive nat
| zero : nat
| succ : nat → nat

structure unification_constraint :=
{α : Type u} (lhs : α) (rhs : α)

infix ` ≟ `:50   := unification_constraint.mk
infix ` =?= `:50 := unification_constraint.mk

structure unification_hint :=
(pattern : unification_constraint)
(constraints : list unification_constraint)

/- Declare builtin and reserved notation -/

class has_zero     (α : Type u) := (zero : α)
class has_one      (α : Type u) := (one : α)
class has_add      (α : Type u) := (add : α → α → α)
class has_mul      (α : Type u) := (mul : α → α → α)
class has_inv      (α : Type u) := (inv : α → α)
class has_neg      (α : Type u) := (neg : α → α)
class has_sub      (α : Type u) := (sub : α → α → α)
class has_div      (α : Type u) := (div : α → α → α)
class has_dvd      (α : Type u) := (dvd : α → α → Prop)
class has_mod      (α : Type u) := (mod : α → α → α)
class has_le       (α : Type u) := (le : α → α → Prop)
class has_lt       (α : Type u) := (lt : α → α → Prop)
class has_append   (α : Type u) := (append : α → α → α)
class has_andthen  (α : Type u) := (andthen : α → α → α)
class has_union    (α : Type u) := (union : α → α → α)
class has_inter    (α : Type u) := (inter : α → α → α)
class has_sdiff    (α : Type u) := (sdiff : α → α → α)
class has_subset   (α : Type u) := (subset : α → α → Prop)
class has_ssubset  (α : Type u) := (ssubset : α → α → Prop)
/- Type classes has_emptyc and has_insert are
   used to implement polymorphic notation for collections.
   Example: {a, b, c}. -/
class has_emptyc   (α : Type u) := (emptyc : α)
class has_insert   (α : out_param (Type u)) (γ : Type v) := (insert : α → γ → γ)
/- Type class used to implement the notation { a ∈ c | p a } -/
class has_sep (α : out_param (Type u)) (γ : Type v) :=
(sep : (α → Prop) → γ → γ)
/- Type class for set-like membership -/
class has_mem (α : out_param (Type u)) (γ : Type v) := (mem : α → γ → Prop)

def zero     {α : Type u} [has_zero α]     : α            := has_zero.zero α
def one      {α : Type u} [has_one α]      : α            := has_one.one α
def add      {α : Type u} [has_add α]      : α → α → α    := has_add.add
def mul      {α : Type u} [has_mul α]      : α → α → α    := has_mul.mul
def sub      {α : Type u} [has_sub α]      : α → α → α    := has_sub.sub
def div      {α : Type u} [has_div α]      : α → α → α    := has_div.div
def dvd      {α : Type u} [has_dvd α]      : α → α → Prop := has_dvd.dvd
def mod      {α : Type u} [has_mod α]      : α → α → α    := has_mod.mod
def neg      {α : Type u} [has_neg α]      : α → α        := has_neg.neg
def inv      {α : Type u} [has_inv α]      : α → α        := has_inv.inv
def le       {α : Type u} [has_le α]       : α → α → Prop := has_le.le
def lt       {α : Type u} [has_lt α]       : α → α → Prop := has_lt.lt
def append   {α : Type u} [has_append α]   : α → α → α    := has_append.append
def andthen  {α : Type u} [has_andthen α]  : α → α → α    := has_andthen.andthen
def union    {α : Type u} [has_union α]    : α → α → α    := has_union.union
def inter    {α : Type u} [has_inter α]    : α → α → α    := has_inter.inter
def sdiff    {α : Type u} [has_sdiff α]    : α → α → α    := has_sdiff.sdiff
def subset   {α : Type u} [has_subset α]   : α → α → Prop := has_subset.subset
def ssubset  {α : Type u} [has_ssubset α]  : α → α → Prop := has_ssubset.ssubset
@[reducible]
def ge {α : Type u} [has_le α] (a b : α) : Prop := le b a
@[reducible]
def gt {α : Type u} [has_lt α] (a b : α) : Prop := lt b a
@[reducible]
def superset {α : Type u} [has_subset α] (a b : α) : Prop := subset b a
@[reducible]
def ssuperset {α : Type u} [has_ssubset α] (a b : α) : Prop := ssubset b a
def bit0 {α : Type u} [s  : has_add α] (a  : α)                 : α := add a a
def bit1 {α : Type u} [s₁ : has_one α] [s₂ : has_add α] (a : α) : α := add (bit0 a) one

attribute [pattern] zero one bit0 bit1 add neg

def insert {α : Type u} {γ : Type v} [has_insert α γ] : α → γ → γ :=
has_insert.insert

/- The empty collection -/
def emptyc {α : Type u} [has_emptyc α] : α :=
has_emptyc.emptyc α

def singleton {α : Type u} {γ : Type v} [has_emptyc γ] [has_insert α γ] (a : α) : γ :=
insert a emptyc

def sep {α : Type u} {γ : Type v} [has_sep α γ] : (α → Prop) → γ → γ :=
has_sep.sep

def mem {α : Type u} {γ : Type v} [has_mem α γ] : α → γ → Prop :=
has_mem.mem

/- num, pos_num instances -/

instance : has_zero num :=
⟨num.zero⟩

instance : has_one num :=
⟨num.pos pos_num.one⟩

instance : has_one pos_num :=
⟨pos_num.one⟩

namespace pos_num
  def is_one : pos_num → bool
  | one := tt
  | _   := ff

  def pred : pos_num → pos_num
  | one        := one
  | (bit1 n)   := bit0 n
  | (bit0 one) := one
  | (bit0 n)   := bit1 (pred n)

  def size : pos_num → pos_num
  | one      := one
  | (bit0 n) := succ (size n)
  | (bit1 n) := succ (size n)

  def add : pos_num → pos_num → pos_num
  | one  b            := succ b
  | a    one          := succ a
  | (bit0 a) (bit0 b) := bit0 (add a b)
  | (bit1 a) (bit1 b) := bit0 (succ (add a b))
  | (bit0 a) (bit1 b) := bit1 (add a b)
  | (bit1 a) (bit0 b) := bit1 (add a b)
end pos_num

instance : has_add pos_num :=
⟨pos_num.add⟩

namespace num
  open pos_num

  def add : num → num → num
  | zero    a       := a
  | b       zero    := b
  | (pos a) (pos b) := pos (pos_num.add a b)
end num

instance : has_add num :=
⟨num.add⟩

def std.priority.default : num := 1000
def std.priority.max     : num := 4294967295

/- nat basic instances -/

namespace nat
  protected def prio := num.add std.priority.default 100

  protected def add : nat → nat → nat
  | a  zero     := a
  | a  (succ b) := succ (add a b)

  /- We mark the following definitions as pattern to make sure they can be used in recursive equations,
     and reduced by the equation compiler. -/
  attribute [pattern] nat.add nat.add._main

  def of_pos_num : pos_num → nat
  | pos_num.one      := succ zero
  | (pos_num.bit0 a) := let r := of_pos_num a in nat.add r r
  | (pos_num.bit1 a) := let r := of_pos_num a in succ (nat.add r r)

  def of_num : num → nat
  | num.zero    := zero
  | (num.pos p) := of_pos_num p
end nat

instance : has_zero nat := ⟨nat.zero⟩

instance : has_one nat := ⟨nat.succ (nat.zero)⟩

instance : has_add nat := ⟨nat.add⟩

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
-/
def std.prec.max   : num := 1024 -- the strength of application, identifiers, (, [, etc.
def std.prec.arrow : num := 25

/-
The next def is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
-/

def std.prec.max_plus :=
num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ
  (num.succ std.prec.max)))))))))

reserve postfix `⁻¹`:std.prec.max_plus  -- input with \sy or \-1 or \inv

infix ∈        := mem
notation a ∉ s := ¬ mem a s
infix +        := add
infix *        := mul
infix -        := sub
infix /        := div
infix ∣        := dvd
infix %        := mod
prefix -       := neg
postfix ⁻¹     := inv
infix <=       := le
infix >=       := ge
infix ≤        := le
infix ≥        := ge
infix <        := lt
infix >        := gt
infix ++       := append
infix ;        := andthen
notation `∅`   := emptyc
infix ∪        := union
infix ∩        := inter
infix ⊆        := subset
infix ⊇        := superset
infix ⊂        := ssubset
infix ⊃        := ssuperset
infix \        := sdiff

notation α × β := prod α β
-- notation for n-ary tuples

/- sizeof -/

class has_sizeof (α : Sort u) :=
(sizeof : α → nat)

def sizeof {α : Sort u} [s : has_sizeof α] : α → nat :=
has_sizeof.sizeof

/-
Declare sizeof instances and lemmas for types declared before has_sizeof.
From now on, the inductive compiler will automatically generate sizeof instances and lemmas.
-/

/- Every type `α` has a default has_sizeof instance that just returns 0 for every element of `α` -/
protected def default.sizeof (α : Sort u) : α → nat
| a := 0

instance default_has_sizeof (α : Sort u) : has_sizeof α :=
⟨default.sizeof α⟩

protected def nat.sizeof : nat → nat
| n := n

instance : has_sizeof nat :=
⟨nat.sizeof⟩

protected def prod.sizeof {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] : (prod α β) → nat
| ⟨a, b⟩ := 1 + sizeof a + sizeof b

instance (α : Type u) (β : Type v) [has_sizeof α] [has_sizeof β] : has_sizeof (prod α β) :=
⟨prod.sizeof⟩

protected def sum.sizeof {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] : (sum α β) → nat
| (sum.inl a) := 1 + sizeof a
| (sum.inr b) := 1 + sizeof b

instance (α : Type u) (β : Type v) [has_sizeof α] [has_sizeof β] : has_sizeof (sum α β) :=
⟨sum.sizeof⟩

protected def sigma.sizeof {α : Type u} {β : α → Type v} [has_sizeof α] [∀ a, has_sizeof (β a)] : sigma β → nat
| ⟨a, b⟩ := 1 + sizeof a + sizeof b

instance (α : Type u) (β : α → Type v) [has_sizeof α] [∀ a, has_sizeof (β a)] : has_sizeof (sigma β) :=
⟨sigma.sizeof⟩

protected def unit.sizeof : unit → nat
| u := 1

instance : has_sizeof unit := ⟨unit.sizeof⟩

protected def punit.sizeof : punit → nat
| u := 1

instance : has_sizeof punit := ⟨punit.sizeof⟩

protected def bool.sizeof : bool → nat
| b := 1

instance : has_sizeof bool := ⟨bool.sizeof⟩

protected def pos_num.sizeof : pos_num → nat
| p := nat.of_pos_num p

instance : has_sizeof pos_num :=
⟨pos_num.sizeof⟩

protected def num.sizeof : num → nat
| n := nat.of_num n

instance : has_sizeof num :=
⟨num.sizeof⟩

protected def option.sizeof {α : Type u} [has_sizeof α] : option α → nat
| none     := 1
| (some a) := 1 + sizeof a

instance (α : Type u) [has_sizeof α] : has_sizeof (option α) :=
⟨option.sizeof⟩

protected def list.sizeof {α : Type u} [has_sizeof α] : list α → nat
| list.nil        := 1
| (list.cons a l) := 1 + sizeof a + list.sizeof l

instance (α : Type u) [has_sizeof α] : has_sizeof (list α) :=
⟨list.sizeof⟩

lemma nat_add_zero (n : nat) : n + 0 = n := rfl

/- Combinator calculus -/
namespace combinator
universes u₁ u₂ u₃
def I {α : Type u₁} (a : α) := a
def K {α : Type u₁} {β : Type u₂} (a : α) (b : β) := a
def S {α : Type u₁} {β : Type u₂} {γ : Type u₃} (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
end combinator

/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude

notation `Prop`  := PType 0
notation `Type₂` := PType 2
notation `Type₃` := PType 3

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

universe variables u v

/- gadget for optional parameter support -/
@[reducible] def opt_param (α : PType u) (default : α) : PType u :=
α

inductive poly_unit : PType u
| star : poly_unit

inductive unit : Type
| star : unit

inductive true : Prop
| intro : true

inductive false : Prop

inductive empty : Type

def not (a : Prop) := a → false
prefix `¬` := not

inductive eq {α : PType u} (a : α) : α → Prop
| refl : eq a

init_quotient

inductive heq {α : PType u} (a : α) : Π {β : PType u}, β → Prop
| refl : heq a

structure prod (α : Type u) (β : Type v) :=
(fst : α) (snd : β)

/- Similar to prod, but α and β can be propositions.
   We use this type internally to automatically generate the brec_on recursor. -/
structure pprod (α : PType u) (β : PType v) :=
(fst : α) (snd : β)

inductive and (a b : Prop) : Prop
| intro : a → b → and

def and.elim_left {a b : Prop} (h : and a b) : a :=
and.rec (λ ha hb, ha) h

def and.left := @and.elim_left

def and.elim_right {a b : Prop} (h : and a b) : b :=
and.rec (λ ha hb, hb) h

def and.right := @and.elim_right

inductive sum (α : Type u) (β : Type v)
| inl {} : α → sum
| inr {} : β → sum

inductive psum (α : PType u) (β : PType v)
| inl {} : α → psum
| inr {} : β → psum

inductive or (a b : Prop) : Prop
| inl {} : a → or
| inr {} : b → or

def or.intro_left {a : Prop} (b : Prop) (ha : a) : or a b :=
or.inl ha

def or.intro_right (a : Prop) {b : Prop} (hb : b) : or a b :=
or.inr hb

structure sigma {α : Type u} (β : α → PType v) :=
mk :: (fst : α) (snd : β fst)

structure psigma {α : PType u} (β : α → PType v) :=
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

class inductive decidable (p : Prop)
| is_false : ¬p → decidable
| is_true :  p → decidable

@[reducible]
def decidable_pred {α : PType u} (r : α → Prop) :=
Π (a : α), decidable (r a)

@[reducible]
def decidable_rel {α : PType u} (r : α → α → Prop) :=
Π (a b : α), decidable (r a b)

@[reducible]
def decidable_eq (α : PType u) :=
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
class has_insert   (α : Type u) (γ : Type u → Type v) := (insert : α → γ α → γ α)
/- Type class used to implement the notation { a ∈ c | p a } -/
class has_sep (α : Type u) (γ : Type u → Type v) :=
(sep : (α → Prop) → γ α → γ α)
/- Type class for set-like membership -/
class has_mem (α : Type u) (γ : Type u → Type v) := (mem : α → γ α → Prop)

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

def insert {α : Type u} {γ : Type u → Type v} [has_insert α γ] : α → γ α → γ α :=
has_insert.insert

/- The empty collection -/
def emptyc {α : Type u} [has_emptyc α] : α :=
has_emptyc.emptyc α

def singleton {α : Type u} {γ : Type u → Type v} [has_emptyc (γ α)] [has_insert α γ] (a : α) : γ α :=
insert a emptyc

def sep {α : Type u} {γ : Type u → Type v} [has_sep α γ] : (α → Prop) → γ α → γ α :=
has_sep.sep

def mem {α : Type u} {γ : Type u → Type v} [has_mem α γ] : α → γ α → Prop :=
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

infix =        := eq
infix ==       := heq
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
notation `(` h `, ` t:(foldr `, ` (e r, prod.mk e r)) `)` := prod.mk h t

/- eq basic support -/

attribute [refl] eq.refl

@[pattern] def rfl {α : PType u} {a : α} : a = a := eq.refl a

@[elab_as_eliminator, subst]
lemma eq.subst {α : PType u} {P : α → Prop} {a b : α} (h₁ : a = b) (h₂ : P a) : P b :=
eq.rec h₂ h₁

notation h1 ▸ h2 := eq.subst h1 h2

@[trans] lemma eq.trans {α : PType u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
h₂ ▸ h₁

@[symm] lemma eq.symm {α : PType u} {a b : α} (h : a = b) : b = a :=
h ▸ rfl

/- sizeof -/

class has_sizeof (α : PType u) :=
(sizeof : α → nat)

def sizeof {α : PType u} [s : has_sizeof α] : α → nat :=
has_sizeof.sizeof

/-
Declare sizeof instances and lemmas for types declared before has_sizeof.
From now on, the inductive compiler will automatically generate sizeof instances and lemmas.
-/

/- Every type `α` has a default has_sizeof instance that just returns 0 for every element of `α` -/
instance default_has_sizeof (α : PType u) : has_sizeof α :=
⟨λ a, nat.zero⟩

/- TODO(Leo): the [simp.sizeof] annotations are not really necessary.
   What we need is a robust way of unfolding sizeof definitions. -/
attribute [simp.sizeof]
lemma default_has_sizeof_eq (α : PType u) (a : α) : @sizeof α (default_has_sizeof α) a = 0 :=
rfl

instance : has_sizeof nat :=
⟨λ a, a⟩

attribute [simp.sizeof]
lemma sizeof_nat_eq (a : nat) : sizeof a = a :=
rfl

protected def prod.sizeof {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] : (prod α β) → nat
| ⟨a, b⟩ := 1 + sizeof a + sizeof b

instance (α : Type u) (β : Type v) [has_sizeof α] [has_sizeof β] : has_sizeof (prod α β) :=
⟨prod.sizeof⟩

attribute [simp.sizeof]
lemma sizeof_prod_eq {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] (a : α) (b : β) : sizeof (prod.mk a b) = 1 + sizeof a + sizeof b :=
rfl

protected def sum.sizeof {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] : (sum α β) → nat
| (sum.inl a) := 1 + sizeof a
| (sum.inr b) := 1 + sizeof b

instance (α : Type u) (β : Type v) [has_sizeof α] [has_sizeof β] : has_sizeof (sum α β) :=
⟨sum.sizeof⟩

attribute [simp.sizeof]
lemma sizeof_sum_eq_left {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] (a : α) : sizeof (@sum.inl α β a) = 1 + sizeof a :=
rfl

attribute [simp.sizeof]
lemma sizeof_sum_eq_right {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] (b : β) : sizeof (@sum.inr α β b) = 1 + sizeof b :=
rfl

protected def sigma.sizeof {α : Type u} {β : α → Type v} [has_sizeof α] [∀ a, has_sizeof (β a)] : sigma β → nat
| ⟨a, b⟩ := 1 + sizeof a + sizeof b

instance (α : Type u) (β : α → Type v) [has_sizeof α] [∀ a, has_sizeof (β a)] : has_sizeof (sigma β) :=
⟨sigma.sizeof⟩

attribute [simp.sizeof]
lemma sizeof_sigma_eq {α : Type u} {β : α → Type v} [has_sizeof α] [∀ a, has_sizeof (β a)] (a : α) (b : β a) : sizeof (@sigma.mk α β a b) = 1 + sizeof a + sizeof b :=
rfl

instance : has_sizeof unit := ⟨λ u, 1⟩

attribute [simp.sizeof]
lemma sizeof_unit_eq (u : unit) : sizeof u = 1 :=
rfl

instance : has_sizeof poly_unit := ⟨λ u, 1⟩

attribute [simp.sizeof]
lemma sizeof_poly_unit_eq (u : poly_unit) : sizeof u = 1 :=
rfl

instance : has_sizeof bool := ⟨λ u, 1⟩

attribute [simp.sizeof]
lemma sizeof_bool_eq (b : bool) : sizeof b = 1 :=
rfl

instance : has_sizeof pos_num :=
⟨nat.of_pos_num⟩

attribute [simp.sizeof]
lemma sizeof_pos_num_eq (p : pos_num) : sizeof p = nat.of_pos_num p :=
rfl

instance : has_sizeof num :=
⟨nat.of_num⟩

attribute [simp.sizeof]
lemma sizeof_num_eq (n : num) : sizeof n = nat.of_num n :=
rfl

protected def option.sizeof {α : Type u} [has_sizeof α] : option α → nat
| none     := 1
| (some a) := 1 + sizeof a

instance (α : Type u) [has_sizeof α] : has_sizeof (option α) :=
⟨option.sizeof⟩

attribute [simp.sizeof]
lemma sizeof_option_none_eq (α : Type u) [has_sizeof α] : sizeof (@none α) = 1 :=
rfl

attribute [simp.sizeof]
lemma sizeof_option_some_eq {α : Type u} [has_sizeof α] (a : α) : sizeof (some a) = 1 + sizeof a :=
rfl

protected def list.sizeof {α : Type u} [has_sizeof α] : list α → nat
| list.nil        := 1
| (list.cons a l) := 1 + sizeof a + list.sizeof l

instance (α : Type u) [has_sizeof α] : has_sizeof (list α) :=
⟨list.sizeof⟩

attribute [simp.sizeof]
lemma sizeof_list_nil_eq (α : Type u) [has_sizeof α] : sizeof (@list.nil α) = 1 :=
rfl

attribute [simp.sizeof]
lemma sizeof_list_cons_eq {α : Type u} [has_sizeof α] (a : α) (l : list α) : sizeof (list.cons a l) = 1 + sizeof a + sizeof l :=
rfl

attribute [simp.sizeof]
lemma nat_add_zero (n : nat) : n + 0 = n := rfl

/- Combinator calculus -/
namespace combinator
universe variables u₁ u₂ u₃
def I {α : Type u₁} (a : α) := a
def K {α : Type u₁} {β : Type u₂} (a : α) (b : β) := a
def S {α : Type u₁} {β : Type u₂} {γ : Type u₃} (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
end combinator

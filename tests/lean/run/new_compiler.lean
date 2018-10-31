import init.lean.parser.parsec
import init.control.coroutine
universes u v w r s

set_option trace.compiler.stage1 true
-- set_option pp.implicit true
set_option pp.binder_types false
set_option pp.proofs true

def foo (n : nat) : nat :=
let x := nat.zero in
let x_1 := nat.succ x in
let x_2 := nat.succ x_1 in
let x_3 := nat.succ x_2 in
let x_4 := nat.succ x_3 in
let x_5 := nat.succ x_4 in
let x_6 := nat.succ x_5 in
let x_7 := nat.succ x   in
let x_8 := nat.succ x_7 in
let y_1 := x in
let y_2 := y_1 in
y_2 + n

def cse_tst (n : nat) : nat :=
let y := nat.succ ((λ x, x) n) in
let z := nat.succ n in
y + z

def tst1 (n : nat) : nat :=
let p := (nat.succ n, n) in
let q := (p, p) in
prod.cases_on q (λ x y, prod.cases_on x (λ z w, z))

def tst2 (n : nat) : nat :=
let p := (λ x, nat.succ x, nat.zero)  in
let f := λ p : (nat → nat) × nat, p.1 in
f p n

def add' : nat → nat → nat
| 0 b     := nat.succ b
| (a+1) b := nat.succ (nat.succ (add' a b))

def aux (i : nat) (h : i > 0) :=
i

def foo2 : nat :=
@false.rec (λ _, nat) sorry

set_option pp.notation false

def foo3 (n : nat) : nat :=
(λ a : nat, a + a + a) (n*n)

def boo (a : nat) (l : list nat) : list nat :=
let f := @list.cons nat in
f a (f a l)

def bla (i : nat) (h : i > 0 ∧ i ≠ 10) : nat :=
@and.rec _ _ (λ _, nat) (λ h₁ h₂, aux i h₁ + aux i h₁) h

def bla' (i : nat) (h : i > 0 ∧ i ≠ 10) : nat :=
@and.cases_on _ _ (λ _, nat) h (λ h₁ h₂, aux i h₁ + aux i h₁)

inductive vec (α : Type u) : nat → Type u
| nil {}  : vec 0
| cons    : Π {n}, α → vec n → vec (nat.succ n)

def vec.map {α β σ : Type u} (f : α → β → σ) : Π {n : nat}, vec α n → vec β n → vec σ n
| _ vec.nil vec.nil                 := vec.nil
| _ (vec.cons a as) (vec.cons b bs) := vec.cons (f a b) (vec.map as bs)

namespace coroutine
variables {α : Type u} {δ : Type v} {β γ : Type w}

def pipe2 : coroutine α δ β → coroutine δ γ β → coroutine α γ β
| (mk k₁) (mk k₂) := mk $ λ a,
  match k₁ a, rfl : ∀ (n : _), n = k₁ a → _ with
  | done b, h        := done b
  | yielded d k₁', h :=
    match k₂ d with
    | done b        := done b
    | yielded r k₂' :=
      -- have direct_subcoroutine k₁' (mk k₁), { apply direct_subcoroutine.mk k₁ a d, rw h },
      yielded r (pipe2 k₁' k₂')

end coroutine

set_option pp.all true
set_option pp.binder_types true

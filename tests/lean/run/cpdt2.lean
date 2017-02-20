/-
CPDT Chapter 2, Introducing Inductive Types
-/
import tools.mini_crush
universe variable u

export nat (succ)

def is_zero : ℕ → bool
| 0        := tt
| (succ _) := ff

def plus : ℕ → ℕ → ℕ
| 0 m         := m
| (succ n') m := succ (plus n' m)

theorem n_plus_0 (n : ℕ) : plus n 0 = n :=
by mini_crush

lemma plus_S (n1 n2 : nat) : plus n1 (succ n2) = succ (plus n1 n2) :=
by mini_crush

inductive nat_list : Type
| NNil  : nat_list
| NCons : nat → nat_list → nat_list

open nat_list

def nlength : nat_list → ℕ
| NNil          := 0
| (NCons _ ls') := succ (nlength ls')

def napp : nat_list → nat_list → nat_list
| NNil ls2 := ls2
| (NCons n ls1') ls2 := NCons n (napp ls1' ls2)

theorem nlength_napp (ls1 ls2 : nat_list) : nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2) :=
by mini_crush

inductive nat_btree : Type
| NLeaf : nat_btree
| NNode : nat_btree → ℕ → nat_btree → nat_btree

open nat_btree

def nsize : nat_btree → ℕ
| NLeaf             := succ 0
| (NNode tr1 _ tr2) := plus (nsize tr1) (nsize tr2)

def nsplice : nat_btree → nat_btree → nat_btree
| NLeaf tr2               := NNode tr2 0 NLeaf
| (NNode tr1' n tr2') tr2 := NNode (nsplice tr1' tr2) n tr2'

@[simp] theorem plus_assoc (n1 n2 n3 : nat) : plus (plus n1 n2) n3 = plus n1 (plus n2 n3) :=
by mini_crush

theorem nsize_nsplice (tr1 tr2 : nat_btree) : nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1) :=
by mini_crush

export list (nil cons)

def length {α : Type u} : list α → ℕ
| nil          := 0
| (cons _ ls') := succ (length ls')

def app {α : Type u} : list α → list α → list α
| nil ls2           := ls2
| (cons x ls1') ls2 := cons x (app ls1' ls2)

theorem length_app {α : Type u} (ls1 ls2 : list α) : length (app ls1 ls2) = plus (length ls1) (length ls2) :=
by mini_crush

inductive pformula : Type
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula → pformula → pformula.

open pformula

def pformula_denote : pformula → Prop
| Truth               := true
| Falsehood           := false
| (Conjunction f1 f2) := pformula_denote f1 ∧ pformula_denote f2

open pformula

inductive formula : Type
| Eq     : nat → nat → formula
| And    : formula → formula → formula
| Forall : (nat → formula) → formula

open formula

example forall_refl : formula := Forall (λ x, Eq x x)

def formula_denote : formula → Prop
| (Eq n1 n2)  := n1 = n2
| (And f1 f2) := formula_denote f1 ∧ formula_denote f2
| (Forall f') := ∀ n : nat, formula_denote (f' n)

def swapper : formula → formula
| (Eq n1 n2)  := Eq n2 n1
| (And f1 f2) := And (swapper f2) (swapper f1)
| (Forall f') := Forall (λ n, swapper (f' n))

theorem swapper_preserves_truth (f) : formula_denote f → formula_denote (swapper f) :=
by mini_crush

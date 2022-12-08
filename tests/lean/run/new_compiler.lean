

universe u v w r s

set_option trace.compiler.stage1 true
-- set_option pp.explicit true
-- set_option pp.proofs true

def foo (n : Nat) : Nat :=
let x := Nat.zero;
let x1 := Nat.succ x;
let x2 := Nat.succ x1;
let x3 := Nat.succ x2;
let x4 := Nat.succ x3;
let x5 := Nat.succ x4;
let x6 := Nat.succ x5;
let x7 := Nat.succ x  ;
let x8 := Nat.succ x7;
let y1 := x;
let y2 := y1;
y2 + n

def cseTst (n : Nat) : Nat :=
let y := Nat.succ ((fun x => x) n);
let z := Nat.succ n;
y + z

def tst1 (n : Nat) : Nat :=
let p := (Nat.succ n, n);
let q := (p, p);
match q with
| ((z, w), y) => z

def tst2 (n : Nat) : Nat :=
let p := (fun x => Nat.succ x, Nat.zero) ;
let f := fun (p : (Nat → Nat) × Nat) => p.1;
f p n

partial def add' : Nat → Nat → Nat
| 0, b     => Nat.succ b
| a+1,   b => Nat.succ (Nat.succ (add' a b))

def aux (i : Nat) (h : i > 0) :=
i

axiom bad (α : Sort u) : α

unsafe def foo2 : Nat :=
@False.rec (fun _ => Nat) (bad _)

set_option pp.notation false

def foo3 (n : Nat) : Nat :=
(fun (a : Nat) => a + a + a) (n*n)

def boo (a : Nat) (l : List Nat) : List Nat :=
let f := @List.cons Nat;
f a (f a l)

def bla (i : Nat) (h : i > 0 ∧ i ≠ 10) : Nat :=
@And.rec _ _ (fun _ => Nat) (fun h₁ h₂ => aux i h₁ + aux i h₁) h

def bla' (i : Nat) (h : i > 0 ∧ i ≠ 10) : Nat :=
@And.casesOn _ _ (fun _ => Nat) h (fun h₁ h₂ => aux i h₁ + aux i h₁)

inductive vec (α : Type u) : Nat → Type u
| nil   : vec α 0
| cons  : ∀ {n}, α → vec α n → vec α (Nat.succ n)

/-
def vec.map {α β σ : Type u} (f : α → β → σ) : ∀ {n : Nat}, vec α n → vec β n → vec σ n
| _, nil, nil               => nil
| _, cons a as, cons b bs   => cons (f a b) (map f as bs)
-/

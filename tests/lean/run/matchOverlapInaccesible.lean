set_option warn.sorry false

inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

axiom nDiv2 (n : Nat)     : n % 2 = 0 → n = n/2 + n/2
axiom nDiv2Succ (n : Nat) : n % 2 ≠ 0 → n = Nat.succ (n/2 + n/2)

def parity (n : Nat) : Parity n :=
if h : n % 2 = 0 then
  Eq.ndrec (Parity.even (n/2)) (nDiv2 n h).symm
else
  Eq.ndrec (Parity.odd (n/2)) (nDiv2Succ n h).symm

/--
error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  n✝¹.succ = n✝.add n✝
at case `Parity.even` after processing
  (Nat.succ _), _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs in
partial def natToBinBad (n : Nat) : List Bool :=
match n, parity n with
| 0, _             => []
| _, Parity.even j => false :: natToBinBad j
| _, Parity.odd  j => true  :: natToBinBad j


inductive MyNat : Type where
| zero : MyNat
| succ : MyNat -> MyNat

def MyNat.add : MyNat -> MyNat -> MyNat := sorry
instance : Add MyNat where
  add := MyNat.add

namespace MyNat

inductive Parity : MyNat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (MyNat.succ (n + n))

def parity (n : MyNat) : Parity n := sorry

set_option trace.Meta.Match.match true

/--
error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  a✝.succ = sorry n✝ n✝
at case `Parity.even` after processing
  (succ _), _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs(pass trace, all) in
partial def myNatToBinBad (n : MyNat) : List Bool :=
match n, parity n with
| zero, _             => []
| _, Parity.even j => false :: myNatToBinBad j
| _, Parity.odd  j => true  :: myNatToBinBad j

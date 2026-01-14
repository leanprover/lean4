set_option linter.unusedVariables false
--

def h1 (b : Bool) : Nat :=
match b with
| true  => 0
| false => 10

/-- info: 10 -/
#guard_msgs in
#eval h1 false

def h2 (x : List Nat) : Nat :=
match x with
| [x1, x2] => x1 + x2
| x::xs    => x
| _        => 0

/-- info: 10 -/
#guard_msgs in
#eval h1 false
/-- info: 3 -/
#guard_msgs in
#eval h2 [1, 2]
/-- info: 10 -/
#guard_msgs in
#eval h2 [10, 4, 5]
/-- info: 0 -/
#guard_msgs in
#eval h2 []

def h3 (x : Array Nat) : Nat :=
  match x with
  | #[x]    => x
  | #[x, y] => x + y
  | xs      => xs.size

/-- info: 10 -/
#guard_msgs in
#eval h3 #[10]
/-- info: 30 -/
#guard_msgs in
#eval h3 #[10, 20]
/-- info: 4 -/
#guard_msgs in
#eval h3 #[10, 20, 30, 40]

/--
error: Failed to compile pattern matching: Stuck at
  remaining variables: [x✝:(Array Nat)]
  alternatives:
    [x:(Nat)]
    |- [#[x]] => h_1 x
    [x:(Nat), y:(Nat)]
    |- [#[x, y]] => h_2 x y
  examples:_
-/
#guard_msgs in
def h4 (x : Array Nat) : Nat :=
  match x with
  | #[x]    => x
  | #[x, y] => x + y

def h5 (x : String) : Nat :=
  match x with
  | "val1" => 0
  | "val2" => 1
  | _      => 10

inductive Image {α β : Type} (f : α → β) : β → Type
| mk (a : α) : Image f (f a)

def mkImage {α β : Type} (f : α → β) (a : α) : Image f (f a) :=
Image.mk a

def inv {α β : Type} {f : α → β} {b : β} (t : Image f b) : α :=
match b, t with
| _, Image.mk a => a

/-- info: 10 -/
#guard_msgs in
#eval inv (mkImage Nat.succ 10)

theorem foo {p q} (h : p ∨ q) : q ∨ p :=
match h with
| Or.inl h => Or.inr h
| Or.inr h => Or.inl h

def f (x : Nat × Nat) : Bool × Bool × Bool → Nat :=
match x with
| (a, b) => fun _ => a

structure S where
  (x y z : Nat := 0)

def f1 : S → S :=
fun { x := x, ..} => { y := x }

theorem ex2 : f1 { x := 10 } = { y := 10 } :=
rfl

universe u

inductive Vec (α : Type u) : Nat → Type u
| nil : Vec α 0
| cons {n} (head : α) (tail : Vec α n) : Vec α (n+1)

inductive VecPred {α : Type u} (P : α → Prop) : {n : Nat} → Vec α n → Prop
| nil   : VecPred P Vec.nil
| cons  {n : Nat} {head : α} {tail : Vec α n} : P head → VecPred P tail → VecPred P (Vec.cons head tail)

theorem ex3 {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
| _, Vec.cons head _, VecPred.cons h _ => ⟨head, h⟩

/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive 0 (Vec.cons head✝ Vec.nil) ⋯
but is expected to have type
  motive x✝ (Vec.cons head✝ tail✝) ⋯
-/
#guard_msgs in
theorem ex4 {α : Type u} (P : α → Prop) : {n : Nat} → (v : Vec α (n+1)) → VecPred P v → Exists P
| _, Vec.cons head _, VecPred.cons h (w : VecPred P Vec.nil) => ⟨head, h⟩  -- ERROR

axiom someNat : Nat

noncomputable def f2 (x : Nat) := -- must mark as noncomputable since it uses axiom `someNat`
x + someNat

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

partial def natToBin : (n : Nat) → List Bool
| 0 => []
| n => match n, parity n with
  | _, Parity.even j => false :: natToBin j
  | _, Parity.odd  j => true  :: natToBin j

/-- info: [false, true, true] -/
#guard_msgs in
#eval natToBin 6

partial def natToBin' : (n : Nat) → List Bool
| 0 => []
| n => match parity n with
  | Parity.even j => false :: natToBin j
  | Parity.odd  j => true  :: natToBin j

-- This used to be bad until we used sparse matchers,
-- which meant that the `0` pattern does not cause the remaining
-- to have `n = .succ _`, whic breaks dependent pattern matching
partial def natToBinBad (n : Nat) : List Bool :=
match n, parity n with
| 0, _             => []
| _, Parity.even j => false :: natToBin j
| _, Parity.odd  j => true  :: natToBin j

-- The refactoring #11695 also fixed this, because it is more likely to use
-- value matching when it sees no actual constructors. Previously, the
-- inaccessible pattern caused it to expand the literal to a constructor.

set_option backward.match.sparseCases false in
#guard_msgs in
partial def natToBinBadOld (n : Nat) : List Bool :=
match n, parity n with
| 0, _             => []
| _, Parity.even j => false :: natToBin j
| _, Parity.odd  j => true  :: natToBin j

-- Somehow the refactoring in #11695 also made this work, because
-- `.succ 0` is treated as a value, not as a constructor pattern

partial def natToBinBad2 (n : Nat) : List Bool :=
match n, parity n with
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => false :: natToBin j
| _, Parity.odd  j => true  :: natToBin j

-- To still see the problem we have to make sure we do a constructor match:

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
#guard_msgs(pass trace, all) in
partial def natToBinBad3 (n : Nat) : List Bool :=
match n, parity n with
| .succ (.succ n), _ => [true]
| 0, _               => []
| _, Parity.even j   => false :: natToBin j
| _, Parity.odd  j   => true  :: natToBin j

partial def natToBin2 (n : Nat) : List Bool :=
match n, parity n with
| _, Parity.even 0 => []
| _, Parity.even j => false :: natToBin j
| _, Parity.odd  j => true  :: natToBin j

/-- info: [false, true, true] -/
#guard_msgs in
#eval natToBin2 6

partial def natToBin2' (n : Nat) : List Bool :=
match parity n with
| Parity.even 0 => []
| Parity.even j => false :: natToBin j
| Parity.odd  j => true  :: natToBin j

/--
error: Invalid match expression: The type of pattern variable 'a' contains metavariables:
  ?m.12
---
info: fun x => ?m.3 : ?m.12 × ?m.13 → ?m.12
-/
#guard_msgs in
#check fun (a, b) => a -- Error type of pattern variable contains metavariables

/--
info: fun x =>
  match x with
  | (a, b) => a + b : Nat × Nat → Nat
-/
#guard_msgs in
#check fun (a, b) => (a:Nat) + b

/--
info: fun x =>
  match x with
  | (a, b) => a && b : Bool × Bool → Bool
-/
#guard_msgs in
#check fun (a, b) => a && b

/--
info: fun x =>
  match x with
  | (a, b) => a + b : Nat × Nat → Nat
-/
#guard_msgs in
#check fun ((a : Nat), (b : Nat)) => a + b

/--
info: fun x x_1 =>
  match x, x_1 with
  | some a, some b => some (a + b)
  | x, x_2 => none : Option Nat → Option Nat → Option Nat
-/
#guard_msgs in
#check fun
  | some a, some b => some (a + b : Nat)
  | _,      _      => none

-- overapplied matcher
/--
info: fun x =>
  (match (motive := Nat → Nat → Nat) x with
    | 0 => id
    | x.succ => id)
    x : Nat → Nat
-/
#guard_msgs in
#check fun x => (match x with | 0 => id | x+1 => id) x

#guard_msgs(drop info) in
#check fun
  | #[1, 2]    => 2
  | #[]        => 0
  | #[3, 4, 5] => 3
  | _          => 4

-- underapplied matcher
def g {α} : List α → Nat
  | [a] => 1
  | _   => 0

/--
info: g.match_1.{u_1, u_2} {α : Type u_1} (motive : List α → Sort u_2) (x✝ : List α) (h_1 : (a : α) → motive [a])
  (h_2 : (x : List α) → motive x) : motive x✝
-/
#guard_msgs in
#check g.match_1

#guard_msgs(drop info) in
#check fun (e : Empty) => (nomatch e : False)


inductive N : Type where
| zero : N
| succ (n : N) : N

opaque double (n : N) : N := .zero

inductive Parity : N -> Type
| even (n) : Parity (double n)
| odd  (n) : Parity (N.succ (double n))

-- set_option trace.Meta.Match.matchEqs true


partial def natToBin3 : (n : N) → Parity n →  List Bool
| .zero, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

/--
info: private theorem natToBin3.match_1.congr_eq_1.{u_1} : ∀ (motive : (x : N) → Parity x → Sort u_1) (x : N) (x_1 : Parity x)
  (h_1 : (x : Parity N.zero) → motive N.zero x) (h_2 : (j : N) → motive (double j) (Parity.even j))
  (h_3 : (j : N) → motive (double j).succ (Parity.odd j)) (x_2 : Parity N.zero),
  x = N.zero →
    x_1 ≍ x_2 →
      (match x, x_1 with
        | N.zero, x => h_1 x
        | .(double j), Parity.even j => h_2 j
        | .((double j).succ), Parity.odd j => h_3 j) ≍
        h_1 x_2
-/
#guard_msgs(pass trace, all) in
#print sig natToBin3.match_1.congr_eq_1

/--
error: Failed to realize constant natToBin3.match_1.eq_1:
  failed to solve overlap assumption, unsolved subgoal
    case x
    motive : (x : N) → Parity x → Sort ?u.191
    h_1 : (x : Parity N.zero) → motive N.zero x
    h_2 :
      (j : N) →
        (∀ (x : Parity N.zero), double j = N.zero → Parity.even j ≍ x → False) → motive (double j) (Parity.even j)
    h_3 : (j : N) → motive (double j).succ (Parity.odd j)
    n✝ : N
    h✝ : Nat.hasNotBit 1 (double n✝).ctorIdx
    x✝² : Parity N.zero
    x✝¹ : double n✝ = N.zero
    x✝ : Parity.even n✝ ≍ x✝²
    ⊢ False
---
error: Unknown constant `natToBin3.match_1.eq_1`
-/
#guard_msgs(pass trace, all) in
#print sig natToBin3.match_1.eq_1

-- set_option trace.Meta.Match.matchEqs true
-- set_option trace.Kernel true
-- set_option Elab.async false

def f : List Nat → List Nat → Nat
  | _, 1 :: _ :: _ => 1
  | _, a :: _ => if a > 1 then 2 else 3
  | _, _  => 0

/--
info: private theorem f.match_1.eq_2.{u_1} : ∀ (motive : List Nat → List Nat → Sort u_1) (x : List Nat) (a : Nat)
  (tail : List Nat) (h_1 : (x : List Nat) → (head : Nat) → (tail : List Nat) → motive x (1 :: head :: tail))
  (h_2 : (x : List Nat) → (a : Nat) → (tail : List Nat) → motive x (a :: tail))
  (h_3 : (x x_1 : List Nat) → motive x x_1),
  (∀ (head : Nat) (tail_1 : List Nat), a = 1 → tail = head :: tail_1 → False) →
    (match x, a :: tail with
      | x, 1 :: head :: tail => h_1 x head tail
      | x, a :: tail => h_2 x a tail
      | x, x_1 => h_3 x x_1) =
      h_2 x a tail
-/
#guard_msgs(pass trace, all) in
#print sig f.match_1.eq_2

/--
info: private theorem f.match_1.congr_eq_2.{u_1} : ∀ (motive : List Nat → List Nat → Sort u_1) (x x_1 : List Nat)
  (h_1 : (x : List Nat) → (head : Nat) → (tail : List Nat) → motive x (1 :: head :: tail))
  (h_2 : (x : List Nat) → (a : Nat) → (tail : List Nat) → motive x (a :: tail))
  (h_3 : (x x_2 : List Nat) → motive x x_2) (x_2 : List Nat) (a : Nat) (tail : List Nat),
  x = x_2 →
    x_1 = a :: tail →
      (∀ (head : Nat) (tail_1 : List Nat), a = 1 → tail = head :: tail_1 → False) →
        (match x, x_1 with
          | x, 1 :: head :: tail => h_1 x head tail
          | x, a :: tail => h_2 x a tail
          | x, x_3 => h_3 x x_3) ≍
          h_2 x_2 a tail
-/
#guard_msgs(pass trace, all) in
#print sig f.match_1.congr_eq_2

/--
info: private theorem f.match_1.congr_eq_3.{u_1} : ∀ (motive : List Nat → List Nat → Sort u_1) (x x_1 : List Nat)
  (h_1 : (x : List Nat) → (head : Nat) → (tail : List Nat) → motive x (1 :: head :: tail))
  (h_2 : (x : List Nat) → (a : Nat) → (tail : List Nat) → motive x (a :: tail))
  (h_3 : (x x_2 : List Nat) → motive x x_2) (x_2 x_3 : List Nat),
  x = x_2 →
    x_1 = x_3 →
      (∀ (head : Nat) (tail : List Nat), x_3 = 1 :: head :: tail → False) →
        (∀ (a : Nat) (tail : List Nat), x_3 = a :: tail → False) →
          (match x, x_1 with
            | x, 1 :: head :: tail => h_1 x head tail
            | x, a :: tail => h_2 x a tail
            | x, x_4 => h_3 x x_4) ≍
            h_3 x_2 x_3
-/
#guard_msgs(pass trace, all) in
#print sig f.match_1.congr_eq_3

set_option linter.unusedVariables false in
def testMe (n : Nat) : Bool :=
  match _ : n - 2 with
  | 0 => true
  | m => false

/--
info: private theorem testMe.match_1.congr_eq_1.{u_1} : ∀ (motive : Nat → Sort u_1) (x : Nat) (h_1 : x = 0 → motive 0)
  (h_2 : (m : Nat) → x = m → motive m) (heq : x = 0),
  (match h : x with
    | 0 => h_1 h
    | m => h_2 m h) ≍
    h_1 heq
-/
#guard_msgs(pass trace, all) in
#print sig testMe.match_1.congr_eq_1

 structure DefaultClause (n : Nat) where
  a : List (Fin n)
  b : a.Nodup
  c : a.Nodup

-- set_option  trace.Meta.Match.matchEqs true

def deleteOne {n : Nat} (f : Option (DefaultClause n))  : Nat :=
  match f with
    | none => 0
    | some ⟨[_l], _, _⟩ => 1
    | some _ => 2

/--
info: private theorem deleteOne.match_1.congr_eq_3.{u_1} : ∀ {n : Nat} (motive : Option (DefaultClause n) → Sort u_1)
  (f : Option (DefaultClause n)) (h_1 : Unit → motive none)
  (h_2 : (_l : Fin n) → (b c : [_l].Nodup) → motive (some { a := [_l], b := b, c := c }))
  (h_3 : (val : DefaultClause n) → motive (some val)) (val : DefaultClause n),
  f = some val →
    (∀ (_l : Fin n) (b c : [_l].Nodup), val = { a := [_l], b := b, c := c } → False) →
      (match f with
        | none => h_1 ()
        | some { a := [_l], b := b, c := c } => h_2 _l b c
        | some val => h_3 val) ≍
        h_3 val
-/
#guard_msgs(pass trace, all) in
#print sig deleteOne.match_1.congr_eq_3

set_option trace.Meta.Match.matchEqs true

def foo2 : Nat → Nat → Nat
  | .succ _, 1 => 0
  | .succ _, 2 => 1
  | _,       3 => 2
  | .succ _, 4 => 3
  | _,       5 => 4
  | _, .succ _ => 5
  | _, _       => 6

#print sig foo2.match_1.eq_6

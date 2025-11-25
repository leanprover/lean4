set_option linter.unusedVariables false

inductive N where | z | s (n : N)

set_option backwards.match.sparseCases false
-- set_option trace.Meta.Match.match true in
-- set_option debug.skipKernelTC true
-- set_option trace.Meta.Match.matchEqs true
set_option pp.proofs true

def anyTwo : N → N → Bool
  | .z,    .z    => false
  | .s .z, _     => true
  | _,     .s .z => true
  | _,     _     => false

/--
info: def anyTwo.match_1.{u_1} : (motive : N → N → Sort u_1) →
  (x x_1 : N) →
    (Unit → motive N.z N.z) →
      ((x : N) → motive N.z.s x) → ((x : N) → motive x N.z.s) → ((x x_2 : N) → motive x x_2) → motive x x_1 :=
fun motive x x_1 h_1 h_2 h_3 h_4 =>
  have cont_2 := fun x_2 => N.casesOn x_1 (h_4 x N.z) fun n => N.casesOn n (h_3 x) fun n => h_4 x n.s.s;
  N.casesOn (motive := fun x => (Unit → motive x x_1) → motive x x_1) x
    (fun cont_2 =>
      N.casesOn (motive := fun x => (Unit → motive N.z x) → motive N.z x) x_1 (fun cont_2 => h_1 ())
        (fun n cont_2 => cont_2 ()) cont_2)
    (fun n cont_2 =>
      N.casesOn (motive := fun x => (Unit → motive x.s x_1) → motive x.s x_1) n (fun cont_2 => h_2 x_1)
        (fun n cont_2 => cont_2 ()) cont_2)
    cont_2
-/
#guard_msgs in
#print anyTwo.match_1

inductive Parity : Nat -> Type
| even (n) : Parity (n + n)
| odd  (n) : Parity (Nat.succ (n + n))

set_option match.ignoreUnusedAlts true  in
partial def natToBin : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]
| _, _ => []

-- No eqns, #11342
/--
error: Failed to realize constant natToBin.match_1.splitter:
  failed to generate equality theorem `_private.lean.run.issue11104.0.natToBin.match_1.eq_3` for `match` expression `natToBin.match_1`
  motive✝ : (x : Nat) → Parity x → Sort u_1
  j✝ : Nat
  h_1✝ : (x : Parity 0) → motive✝ 0 x
  h_2✝ : (x : Parity (Nat.succ 0)) → motive✝ 1 x
  h_3✝ : (j : Nat) → motive✝ (j + j) (Parity.even j)
  h_4✝ : (j : Nat) → motive✝ (j + j).succ (Parity.odd j)
  h_5✝ : (x : Nat) → (x_1 : Parity x) → motive✝ x x_1
  x✝¹ : ∀ (x : Parity 0), j✝ + j✝ = 0 → Parity.even j✝ ≍ x → False
  x✝ : ∀ (x : Parity (Nat.succ 0)), j✝ + j✝ = 1 → Parity.even j✝ ≍ x → False
  ⊢ (Nat.rec (motive := fun x => (x_1 : Parity x) → (Unit → motive✝ x x_1) → motive✝ x x_1) (fun x cont_2 => h_1✝ x)
        (fun n n_ih =>
          (fun n x cont_2 =>
              if h_1 : n = 0 then
                Eq.ndrec (motive := fun n => (x : Parity n.succ) → (Unit → motive✝ n.succ x) → motive✝ n.succ x)
                  (fun x cont_2 => Eq.symm h_1 ▸ h_2✝ x) (Eq.symm h_1) x cont_2
              else cont_2 ())
            n)
        (j✝ + j✝) (Parity.even j✝) fun x =>
        Parity.casesOn (motive := fun a x => j✝ + j✝ = a → Parity.even j✝ ≍ x → motive✝ (j✝ + j✝) (Parity.even j✝))
          (Parity.even j✝)
          (fun n h =>
            Eq.ndrec (motive := fun x => (x_1 : Parity x) → x_1 ≍ Parity.even n → motive✝ x x_1)
              (fun x h => Eq.symm (eq_of_heq h) ▸ h_3✝ n) (Eq.symm h) (Parity.even j✝))
          (fun n h =>
            Eq.ndrec (motive := fun x => (x_1 : Parity x) → x_1 ≍ Parity.odd n → motive✝ x x_1)
              (fun x h => Eq.symm (eq_of_heq h) ▸ h_4✝ n) (Eq.symm h) (Parity.even j✝))
          (Eq.refl (j✝ + j✝)) (HEq.refl (Parity.even j✝))) =
      h_3✝ j✝
---
error: Unknown constant `natToBin.match_1.splitter`
-/
#guard_msgs(pass trace, all) in
#print sig natToBin.match_1.splitter


-- This fails because we do the match division only when there is a catch all

/--
error: Tactic `cases` failed with a nested error:
Dependent elimination failed: Failed to solve equation
  n✝¹.succ.succ = n✝.add n✝
at case `Parity.even` after processing
  (Nat.succ (Nat.succ _)), _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs in
partial def natToBin2 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| .succ 0, _       => [true]
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

-- Just to confirm that match division is relevant here

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
set_option backwards.match.divide false in
partial def natToBin3 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]


partial def foo2 : Nat → Nat → Nat
  | .succ n, 1 => foo2 n 1
  | .succ n, 2 => foo2 (.succ n) 1
  | n,       3 => foo2 (.succ n) 2
  | .succ n, 4 => foo2 (if n > 10 then n else .succ n) 3
  | n,       5 => foo2 (n - 1) 4
  | n, .succ m => foo2 n m
  | _, _ => 0

/--
error: Failed to realize constant foo2.match_1.splitter:
  failed to generate equality theorem `_private.lean.run.issue11104.0.foo2.match_1.eq_6` for `match` expression `foo2.match_1`
  case succ.isTrue
  motive✝ : Nat → Nat → Sort u_1
  m✝ : Nat
  h_1✝ : (n : Nat) → motive✝ n.succ 1
  h_2✝ : (n : Nat) → motive✝ n.succ 2
  h_3✝ : (n : Nat) → motive✝ n 3
  h_4✝ : (n : Nat) → motive✝ n.succ 4
  h_5✝ : (n : Nat) → motive✝ n 5
  h_6✝ : (n m : Nat) → motive✝ n m.succ
  h_7✝ : (x x_1 : Nat) → motive✝ x x_1
  x✝⁴ : m✝ = 2 → False
  x✝³ : m✝ = 4 → False
  n✝ : Nat
  x✝² : ∀ (n : Nat), n✝.succ = n.succ → m✝ = 0 → False
  x✝¹ : ∀ (n : Nat), n✝.succ = n.succ → m✝ = 1 → False
  x✝ : ∀ (n : Nat), n✝.succ = n.succ → m✝ = 3 → False
  h✝ : m✝.succ = 1
  ⊢ ((Eq.symm h✝ ▸ fun cont_2 => Eq.symm h✝ ▸ h_1✝ n✝) fun x =>
        Nat.casesOn m✝.succ (h_7✝ n✝.succ Nat.zero) fun n =>
          have cont_5 := fun x => h_6✝ n✝.succ n;
          if h_1 : n = 2 then
            Eq.ndrec (motive := fun n => (Unit → motive✝ n✝.succ n.succ) → motive✝ n✝.succ n.succ)
              (fun cont_5 => Eq.symm h_1 ▸ h_3✝ n✝.succ) (Eq.symm h_1) cont_5
          else
            if h_2 : n = 3 then
              Eq.ndrec (motive := fun n => (Unit → motive✝ n✝.succ n.succ) → ¬n = 2 → motive✝ n✝.succ n.succ)
                (fun cont_5 h_1 =>
                  Eq.symm h_2 ▸
                    Nat.casesOn (motive := fun x => (Unit → motive✝ x (Nat.succ 3)) → motive✝ x (Nat.succ 3)) n✝.succ
                      (fun cont_5 => cont_5 ()) (fun n cont_5 => h_4✝ n) cont_5)
                (Eq.symm h_2) cont_5 h_1
            else
              if h_3 : n = 4 then
                Eq.ndrec (motive := fun n => (Unit → motive✝ n✝.succ n.succ) → ¬n = 2 → ¬n = 3 → motive✝ n✝.succ n.succ)
                  (fun cont_5 h_1 h_2 => Eq.symm h_3 ▸ h_5✝ n✝.succ) (Eq.symm h_3) cont_5 h_1 h_2
              else cont_5 ()) =
      h_6✝ n✝.succ m✝
---
error: Unknown constant `foo2.match_1.splitter`
-/
#guard_msgs in
#print sig foo2.match_1.splitter

def mixed_matches_pure (f : Nat → Option Nat) : Nat :=
  match h : f 0, f 10 with
  | some y, some z => 1
  | _, some _ => 2
  | _, _ => 3

inductive Inline (α : Type u) where
  | concat : Array (Inline α) → Inline α
  | leaf : Inline α

def Inline.append : (x y : Inline α) → Inline α
    | .concat #[], x => x
    | x, .concat #[] => x
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, x => .concat (xs.push x)
    | x, .concat xs => .concat (#[x] ++ xs)
    | x, y => .concat #[x, y]

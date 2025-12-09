opaque double (n : Nat) : Nat

inductive Parity : Nat -> Type
| even (n) : Parity (double n)
| odd  (n) : Parity (Nat.succ (double n))

-- set_option trace.Meta.Match.matchEqs true

partial def natToBin3 : (n : Nat) → Parity n →  List Bool
| 0, _             => []
| _, Parity.even j => [false, false]
| _, Parity.odd  j => [true, true]

/--
info: private theorem natToBin3.match_1.congr_eq_1.{u_1} : ∀ (motive : (x : Nat) → Parity x → Sort u_1) (x : Nat)
  (x_1 : Parity x) (h_1 : (x : Parity 0) → motive 0 x) (h_2 : (j : Nat) → motive (double j) (Parity.even j))
  (h_3 : (j : Nat) → motive (double j).succ (Parity.odd j)) (x_2 : Parity 0),
  x = 0 →
    x_1 ≍ x_2 →
      (match x, x_1 with
        | 0, x => h_1 x
        | .(double j), Parity.even j => h_2 j
        | .((double j).succ), Parity.odd j => h_3 j) ≍
        h_1 x_2
-/
#guard_msgs(pass trace, all) in
#print sig natToBin3.match_1.congr_eq_1

/--
error: Failed to realize constant natToBin3.match_1.eq_1:
  failed to generate equality theorem _private.lean.run.issue11342.0.natToBin3.match_1.eq_2 for `match` expression `natToBin3.match_1`
  motive✝ : (x : Nat) → Parity x → Sort u_1
  j✝ : Nat
  h_1✝ : (x : Parity 0) → motive✝ 0 x
  h_2✝ : (j : Nat) → motive✝ (double j) (Parity.even j)
  h_3✝ : (j : Nat) → motive✝ (double j).succ (Parity.odd j)
  x✝ : ∀ (x : Parity 0), double j✝ = 0 → Parity.even j✝ ≍ x → False
  ⊢ natToBin3._sparseCasesOn_1 (motive := fun x => (x_1 : Parity x) → motive✝ x x_1) (double j✝) (fun x => h_1✝ x)
        (fun h x =>
          Parity.casesOn (motive := fun a x_1 => double j✝ = a → x ≍ x_1 → motive✝ (double j✝) x) x
            (fun n h_1 =>
              Eq.ndrec (motive := fun x =>
                Nat.hasNotBit 1 x.ctorIdx → (x_1 : Parity x) → x_1 ≍ Parity.even n → motive✝ x x_1)
                (fun h x h_2 => ⋯ ▸ h_2✝ n) ⋯ h x)
            (fun n h_1 =>
              Eq.ndrec (motive := fun x =>
                Nat.hasNotBit 1 x.ctorIdx → (x_1 : Parity x) → x_1 ≍ Parity.odd n → motive✝ x x_1)
                (fun h x h_2 => ⋯ ▸ h_3✝ n) ⋯ h x)
            ⋯ ⋯)
        (Parity.even j✝) =
      h_2✝ j✝
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
      | x, x_2 => h_3 x x_2) =
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

-- set_option trace.Meta.Match.matchEqs true

set_option linter.unusedVariables false in
def testMe (n : Nat) : Bool :=
  match _ : n - 2 with
  | 0 => true
  | m => false

/--
info: private theorem testMe.match_1.congr_eq_2.{u_1} : ∀ (motive : Nat → Sort u_1) (x : Nat) (h_1 : x = 0 → motive 0)
  (h_2 : (m : Nat) → x = m → motive m) (m : Nat) (heq : x = m),
  (m = 0 → False) →
    (match h : x with
      | 0 => h_1 h
      | m => h_2 m h) ≍
      h_2 m heq
-/
#guard_msgs(pass trace, all) in
#print sig testMe.match_1.congr_eq_2


inductive Vector' (α : Type u): Nat → Type u where
| nil : Vector' α 0
| cons (head : α) (tail : Vector' α n) : Vector' α (n+1)

namespace Vector'

  def nth : ∀{n}, Vector' α n → Fin n → α
  | n+1, cons x xs, ⟨  0, _⟩ => x
  | n+1, cons x xs, ⟨k+1, h⟩ => xs.nth ⟨k, sorry⟩

  def snoc : ∀{n : Nat} (xs : Vector' α n) (x : α), Vector' α (n+1)
  | _, nil,    x' => cons x' nil
  | _, cons x xs, x' => cons x (snoc xs x')

  #print sig nth.match_1.congr_eq_2
  #print sig nth.match_1.eq_2
end

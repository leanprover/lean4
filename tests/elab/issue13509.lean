/-!
Functional induction: a recursive call under `||` in a dependent `match` (#13509). The induction
hypothesis collected under the binders must not confuse `inferMatchType`.
-/

mutual
variable (f: Nat -> Option Nat)
def walk (hf : ∀ n k, f n = some k → k < n) (n : Nat) : Bool :=
  n == 42 ||
  match n with
  | 0 => false
  | m + 1 =>
    match hst : f (m + 1) with
    | some k => step hf (m + 1) k hst
    | none => false
termination_by (n, 1)
decreasing_by exact Prod.Lex.right _ (by omega)
def step (hf : ∀ n k, f n = some k → k < n)
    (n : Nat) (k : Nat) (hst : f n = some k) : Bool :=
  walk hf k
termination_by (n, 0)
decreasing_by exact Prod.Lex.left _ _ (hf _ _ hst)
end

/--
info: walk.induct : ∀ (f : Nat → Option Nat),
  (∀ (n k : Nat), f n = some k → k < n) →
    ∀ (motive1 : Nat → Prop) (motive2 : (n k : Nat) → f n = some k → Prop),
      (∀ (n : Nat),
          (match n with
            | 0 => True
            | m.succ => ∀ (k : Nat) (hst : f (m + 1) = some k), motive2 (m + 1) k hst) →
            motive1 n) →
        (∀ (n k : Nat) (hst : f n = some k), motive1 k → motive2 n k hst) → ∀ (n : Nat), motive1 n
-/
#guard_msgs in
#check @walk.induct

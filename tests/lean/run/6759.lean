/-!
# Match expressions with unnamed equality proofs

https://github.com/leanprover/lean4/issues/6759

Tests that `match` expressions successfully elaborate when providing a hole instead of an identifier
to which to bind the optional equality proof.
-/

def getLast? {α : Type} (a : Array α) : Option α :=
  match _ : a.size with
  | 0 => none
  | m + 1 => some a[m]

/-- info: some 4 -/
#guard_msgs in
#eval getLast? #[3, 4]


def getLasts? {α : Type} (a b : Array α) : Option (α × α) :=
  match _ : a.size, _ : b.size with
  | 0, _ => none
  | _, 0 => none
  | m + 1, n + 1 => some (a[m], b[n])

/-- info: some (4, 5) -/
#guard_msgs in
#eval getLasts? #[3, 4] #[5]


def getLasts?' (a b : Array α) : Option (α × α) :=
  match _ : a.size, h : b.size with
  | 0, _ => none
  | _, 0 => none
  | m + 1, n + 1 => some (a[m], b[n]'(h ▸ Nat.lt.base n))

/-- info: some (4, 5) -/
#guard_msgs in
#eval getLasts?' #[3, 4] #[5]


theorem test_tactic (n : Nat) (h : n - 1 > 2) : n - 1 > 2 := by
  match _ : n - 1 with
  | 0 =>
    have : n - 1 = 0 := by assumption
    rwa [this] at h
  | n' + 1 =>
    have : n - 1 = n' + 1 := by assumption
    rwa [← this]

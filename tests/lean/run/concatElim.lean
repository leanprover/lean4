universe u

def concat {α} : List α → α → List α
  | [],    a => [a]
  | x::xs, a => x :: concat xs a

def last {α} : (xs : List α) → xs ≠ [] → α
  | [],       h => by contradiction
  | [a],      h => a
  | _::a::as, h => last (a::as) (fun h => by injection h)

def dropLast {α} : List α → List α
  | []    => []
  | [a]   => []
  | a::as => a :: dropLast as

variable {α}

theorem concatEq (xs : List α) (h : xs ≠ []) : concat (dropLast xs) (last xs h) = xs := by
  match xs, h with
  | [],  h        => contradiction
  | [x], h        => rfl
  | x₁::x₂::xs, h => simp [concat, last, concatEq (x₂::xs) List.noConfusion]

theorem lengthCons {α} (x : α) (xs : List α) : (x::xs).length = xs.length + 1 :=
  rfl

theorem eqNilOfLengthZero {α} : (xs : List α) → xs.length = 0 → xs = []
  | [],    h => rfl
  | x::xs, h => by rw [lengthCons] at h; contradiction

theorem dropLastLen {α} (xs : List α) : (n : Nat) → xs.length = n+1 → (dropLast xs).length = n := by
  match xs with
  | []    => intros; contradiction
  | [a]   =>
    intro n h
    have : 1 = n + 1 := h
    have : 0 = n := by injection this; assumption
    subst this
    rfl
  | x₁::x₂::xs =>
    intro n h
    cases n with
    | zero   =>
      simp [lengthCons] at h
      injection h
    | succ n =>
      have : (x₁ :: x₂ :: xs).length = xs.length + 2 := by simp [lengthCons]
      have : xs.length = n := by rw [this] at h; injection h with h; injection h with h; assumption
      simp [dropLast, lengthCons, dropLastLen (x₂::xs) xs.length (lengthCons ..), this]

@[inline]
def concatElim {α}
    (motive : List α → Sort u)
    (base   : Unit → motive [])
    (ind    : (xs : List α) → (a : α) → motive xs → motive (concat xs a))
    (xs : List α)
    : motive xs :=
  let rec @[specialize] aux : (n : Nat) → (xs : List α) → xs.length = n → motive xs
    | 0, xs, h   => by
      have aux := eqNilOfLengthZero _ h
      subst aux
      apply base ()
    | n+1, xs, h => by
      have notNil : xs ≠ [] := by intro h1; subst h1; injection h
      let ih  := aux n (dropLast xs) (dropLastLen _ _ h)
      let aux := ind (dropLast xs) (last xs notNil) ih
      rw [concatEq] at aux
      exact aux
  aux xs.length xs rfl

-- The generated code is tail recursive
def test (xs : List Nat) : IO Unit :=
  concatElim (motive := fun _ => IO Unit)
    (fun _ => pure ())
    (fun xs x r => do IO.println s!"step xs: {xs} x: {x}"; r)
    xs

#eval test [1, 2, 3, 4]

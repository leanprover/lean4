/-!
Test a simplifier issue. `simpApp` first tries to `reduce` the term. If the
term is reduce, pre-simp rules should be tried again before trying to use
congruence. In the following example, the term `g (a + <num>)` takes an
exponential amount of time to be simplified when the pre-simp rules are not
tried before applying congruence.
-/

def myid (x : Nat) := 0 + x

@[simp] theorem myid_eq : myid x = x := by simp [myid]

def myif (c : Prop) [Decidable c] (a b : α) : α :=
  if c then a else b

@[simp ↓] theorem myif_cond_true (c : Prop) {_ : Decidable c} (a b : α) (h : c) : (myif c a b) = a := by
  simp [myif, h]

@[simp ↓] theorem myif_cond_false (c : Prop) {_ : Decidable c} (a b : α) (h : Not c) : (myif c a b) = b := by
  simp [myif, h]

@[congr] theorem myif_congr {x y u v : α} {s : Decidable b} [Decidable c]
    (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : myif b x y = myif c u v := by
  unfold myif
  apply @ite_congr <;> assumption

def f (x : Nat) (y z : Nat) : Nat :=
  myif (myid x = 0) y z

def g (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | a+1 => f x (g a + 1) (g a)

-- `simp` should not be exponential on `g (a + <num>)`
theorem ex (h : a = 1) : g (a+32) = a := by
  simp [g, f, h]

def Nat.bit (b : Bool) (n : Nat) : Nat :=
  cond b (2*n+1) (2*n)

theorem Nat.bit_div_even (h : n % 2 = 0) : bit false (n / 2) = n := by
  simp [bit]
  have := Nat.div_add_mod n 2
  simp [h] at this
  assumption

theorem Nat.bit_div_odd (h : n % 2 ≠ 0) : bit true (n / 2) = n := by
  have h : n % 2 = 1 := by
    have := mod_lt n (by decide : 2 > 0)
    revert h this
    generalize n%2 = k
    match k with
    | 0   => decide
    | 1   => decide
    | n+2 => intros; contradiction
  simp [bit]
  have := Nat.div_add_mod n 2
  simp [h] at this
  assumption

theorem Nat.div2_lt (h : n ≠ 0) : n / 2 < n := by
  match n with
  | 1   => decide
  | 2   => decide
  | 3   => decide
  | n+4 =>
    rw [div_eq, if_pos]
    refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))
    exact @div2_lt (n+2) (by simp +arith)
    simp +arith

@[specialize]
def Nat.binrec
    (motive : Nat → Sort u)
    (base : Unit → motive 0)
    (ind  : (b : Bool) → (n : Nat) → (Unit → motive n) → motive (bit b n))
    (n : Nat) : motive n :=
  if h₁ : n = 0 then
    h₁ ▸ base ()
  else if h₂ : n % 2 = 0 then
    bit_div_even h₂ ▸ ind false (n / 2) (fun _ => binrec motive base ind (n / 2))
  else
    bit_div_odd h₂ ▸ ind true  (n / 2) (fun _ => binrec motive base ind (n / 2))
termination_by n
decreasing_by all_goals exact Nat.div2_lt h₁

theorem Nat.binind
    (motive : Nat → Prop)
    (base : motive 0)
    (ind  : (b : Bool) → (n : Nat) → motive n → motive (bit b n))
    (n : Nat) : motive n :=
 binrec motive (fun _ => base) (fun b n ih => ind b n (ih ())) n

set_option trace.compiler.ir.result true in
def Nat.toBit (n : Nat) : List Bool :=
  binrec (fun _ => List Bool)
    (fun _ => [])
    (fun b n ih => b :: ih ())
    n

#guard Nat.toBit 18 == [false, true, false, false, true]

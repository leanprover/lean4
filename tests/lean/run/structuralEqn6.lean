def trailingZeros (i : Int) : Nat :=
  if h : i = 0 then 0 else aux i.natAbs i h (Nat.le_refl _) 0
where
  aux (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat) : Nat :=
    match k, (by omega : k ≠ 0) with
    | k + 1, _ =>
      if h : i % 2 = 0 then aux k (i / 2) (by omega) (by omega) (acc + 1)
      else acc
  termination_by structural k

/--
info: equations:
@[defeq] theorem trailingZeros.aux.eq_1 : ∀ (i : Int) (hi : i ≠ 0) (acc k_2 : Nat) (x_1 : k_2 + 1 ≠ 0)
  (hk_2 : i.natAbs ≤ k_2 + 1),
  trailingZeros.aux k_2.succ i hi hk_2 acc = if h : i % 2 = 0 then trailingZeros.aux k_2 (i / 2) ⋯ ⋯ (acc + 1) else acc
-/
#guard_msgs(pass trace, all) in
#print equations trailingZeros.aux


-- set_option trace.Elab.definition.eqns true
-- set_option trace.split.debug true
-- set_option trace.Meta.Match.unify true

def trailingZeros' (i : Int) : Nat :=
  if h : i = 0 then 0 else aux i.natAbs i h (Nat.le_refl _) 0
where
  aux (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat) : Nat :=
    match k, (by omega : k ≠ 0) with
    | k + 1, _ =>
      if h : i % 2 = 0 then aux k (i / 2) (by omega) (by omega) (acc + 1)
      else acc
  termination_by k

/--
info: equations:
theorem trailingZeros'.aux.eq_1 : ∀ (i : Int) (hi : i ≠ 0) (acc k_2 : Nat) (x_1 : k_2 + 1 ≠ 0)
  (hk_2 : i.natAbs ≤ k_2 + 1),
  trailingZeros'.aux k_2.succ i hi hk_2 acc =
    if h : i % 2 = 0 then trailingZeros'.aux k_2 (i / 2) ⋯ ⋯ (acc + 1) else acc
-/
#guard_msgs(pass trace, all) in
#print equations trailingZeros'.aux

def trailingZeros2 (i : Int) : Nat :=
  if h : i = 0 then 0 else aux i.natAbs i h (Nat.le_refl _) 0
where
  aux (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat) : Nat :=
    match k  with
    | k + 1 =>
      if h : i % 2 = 0 then aux k (i / 2) (by omega) (by omega) (acc + 1)
      else acc
    | 0 => by omega
  termination_by structural k

/--
info: equations:
@[defeq] theorem trailingZeros2.aux.eq_1 : ∀ (i : Int) (hi : i ≠ 0) (acc k_2 : Nat) (hk_2 : i.natAbs ≤ k_2 + 1),
  trailingZeros2.aux k_2.succ i hi hk_2 acc =
    if h : i % 2 = 0 then trailingZeros2.aux k_2 (i / 2) ⋯ ⋯ (acc + 1) else acc
@[defeq] theorem trailingZeros2.aux.eq_2 : ∀ (i : Int) (hi : i ≠ 0) (acc : Nat) (hk_2 : i.natAbs ≤ 0),
  trailingZeros2.aux 0 i hi hk_2 acc = acc
-/
#guard_msgs(pass trace, all) in
#print equations trailingZeros2.aux

def trailingZeros2' (i : Int) : Nat :=
  if h : i = 0 then 0 else aux i.natAbs i h (Nat.le_refl _) 0
where
  aux (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat) : Nat :=
    match k  with
    | k + 1 =>
      if h : i % 2 = 0 then aux k (i / 2) (by omega) (by omega) (acc + 1)
      else acc
    | 0 => by omega
  termination_by  k

/--
info: equations:
theorem trailingZeros2'.aux.eq_1 : ∀ (i : Int) (hi : i ≠ 0) (acc k_2 : Nat) (hk_2 : i.natAbs ≤ k_2 + 1),
  trailingZeros2'.aux k_2.succ i hi hk_2 acc =
    if h : i % 2 = 0 then trailingZeros2'.aux k_2 (i / 2) ⋯ ⋯ (acc + 1) else acc
@[defeq] theorem trailingZeros2'.aux.eq_2 : ∀ (i : Int) (hi : i ≠ 0) (acc : Nat) (hk_2 : i.natAbs ≤ 0),
  trailingZeros2'.aux 0 i hi hk_2 acc = acc
-/
#guard_msgs(pass trace, all) in
#print equations trailingZeros2'.aux

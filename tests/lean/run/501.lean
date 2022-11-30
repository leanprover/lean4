structure S where
  x : Bool
  y : Nat

def S.Z (s : S) : Type :=
  if s.x then Nat else Int

def S.z : (s : S) → s.Z
  | s@{ x := true, .. } => s.y
  | s@{ x := false, .. } => Int.ofNat s.y

def S.a : (s : S) → s.Z
  | s => s.z

def S.b : (s : S) → s.Z
  | s@h:{ x := true, .. } => h ▸ s.z
  | s => s.z

#check @S.b.match_1

theorem zero_pow : ∀ {m : Nat}, m > 0 → 0 ^ m = 0
  | 0,   h => by cases h
  | _+1, _ => rfl

theorem pow_nonneg : ∀ m : Nat, 0 ^ m ≥ 0
  | 0 => by decide
  | m@(_+1) => by
    rw [zero_pow]
    · decide
    · apply Nat.zero_lt_succ

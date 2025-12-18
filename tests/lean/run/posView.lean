structure Pos where
  protected succ :: protected pred : Nat
  deriving Repr

protected def Pos.add : Pos → Pos → Pos
  | .succ x, .succ y => .succ (x + y).succ

instance : Add Pos := ⟨Pos.add⟩

instance (x : Nat) : OfNat Pos x.succ := ⟨.succ x⟩

/-- View for `Pos` type. -/
inductive PosView where
  | one
  | succ (x : Pos)

/--
  Convert `Pos` into `PosView`.
  Remark: nonrecursive views do not impact performance of the generated code if marked as `[inline]`
 -/
@[inline] def Pos.view (p : Pos) : PosView :=
  match p with
  | { pred := 0 }          => PosView.one
  | { pred := Nat.succ n } => PosView.succ ⟨n⟩

/--
  Helper theorem for proving termination.
  In the future, we should be able to mark it as a forward reasoning theorem for `decreasing_tactic`,
  and it will be applied automatically for us. -/
theorem sizeof_lt_of_view_eq (h : Pos.view p₁ = PosView.succ p₂) : sizeOf p₂ < sizeOf p₁ := by
  match p₁, p₂ with
  | { pred := Nat.succ n }, { pred := Nat.succ m } => simp [Pos.view] at h; simp +arith [h]
  | { pred := Nat.succ n }, { pred := 0 }          => simp [Pos.view] at h; simp +arith [h]
  | { pred := 0 },          _                      => simp [Pos.view] at h

/-- `1` as notation for `PosView.one` -/
instance : OfNat PosView (nat_lit 1) where
  ofNat := PosView.one

def f (p : Pos) : Pos :=
  match h : p.view with -- It would also be nice to have a feature to force Lean to applies "views" automatically for us.
  | 1 => 1
  | .succ x =>
    have : sizeOf x < sizeOf p := sizeof_lt_of_view_eq h -- See comment at `sizeof_lt_of_view_eq`
    f x + x + 1

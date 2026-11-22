/-!
Tests `Acc.rec'`, the replacement for `Acc.rec` at motives that are not propositions. It is
`@[irreducible]` and backed by `Classical.choice`, so unlike `Acc.rec` it has no iota rule.
-/

/-! `Acc.rec'` accepts a motive in any `Sort`, including one mentioning the `Acc` proof. -/

example {α : Type} {r : α → α → Prop} {C : α → Type} {a : α} (h : Acc r a)
    (H : ∀ x, (∀ y, r y x → C y) → C x) : C a :=
  Acc.rec' (motive := fun a _ => C a) (fun x _ ih => H x ih) h

example {α : Type} {r : α → α → Prop} {motive : (a : α) → Acc r a → Type} {a : α} (h : Acc r a)
    (H : ∀ x (hx : ∀ y, r y x → Acc r y), (∀ y hy, motive y (hx y hy)) → motive x (Acc.intro x hx)) :
    motive a h :=
  Acc.rec' H h

/-! The `@[csimp]` rules make all four eliminators compile, despite being `noncomputable`. -/

theorem acc0 : Acc (fun _ _ : Nat => False) 0 := Acc.intro 0 fun _ h => h.elim

/-- info: (0, 0, 0, 0) -/
#guard_msgs in
#eval (Acc.rec' (motive := fun _ _ => Nat) (fun _ _ _ => 0) acc0,
       Acc.recOn' (motive := fun _ _ => Nat) acc0 fun _ _ _ => 0,
       Acc.ndrec' (C := fun _ => Nat) (fun _ _ _ => 0) acc0,
       Acc.ndrecOn' (C := fun _ => Nat) acc0 fun _ _ _ => 0)

/-! `Acc.rec'` has no iota rule, so unfolding equations need `Acc.rec'_eq` rather than `rfl`. -/

noncomputable def fold {α : Type} {r : α → α → Prop} (F : ∀ a, ((b : α) → r b a → Nat) → Nat)
    {a : α} (h : Acc r a) : Nat :=
  Acc.recOn' h fun a _ ih => F a ih

theorem fold_eq {α : Type} {r : α → α → Prop} (F : ∀ a, ((b : α) → r b a → Nat) → Nat)
    {a : α} (h : Acc r a) : fold F h = F a fun _ hb => fold F (h.inv hb) := by
  rw [fold, Acc.recOn', Acc.rec'_eq]
  rfl

/-- info: 'Acc.rec'' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Acc.rec'

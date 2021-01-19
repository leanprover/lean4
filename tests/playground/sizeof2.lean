mutual

  inductive Arg (α : Type u) where
    | val  (a : α)
    | expr (e : Expr α)

  inductive Expr (α : Type u) where
    | app (f : String) (a : List (Arg α))

end

noncomputable def sizeof_1 [SizeOf α] (a : Arg α) :=
  @Arg.rec α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun e ih => 1 + ih)
    (fun f _ ih => 1 + sizeOf f + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable def sizeof_2 [SizeOf α] (a : Expr α) :=
  @Expr.rec α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun e ih => 1 + ih)
    (fun f _ ih => 1 + sizeOf f + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable def sizeof_3 [SizeOf α] (a : List (Arg α)) :=
  @Arg.rec_1 α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun e ih => 1 + ih)
    (fun f _ ih => 1 + sizeOf f + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable instance [SizeOf α] : SizeOf (Arg α) := ⟨sizeof_1⟩

noncomputable instance [SizeOf α] : SizeOf (Expr α) := ⟨sizeof_2⟩

theorem aux_1 [SizeOf α] (a : List (Arg α)) : sizeof_3 a = sizeOf a := by
  induction a with
  | nil => rfl
  | cons h t ih =>
    show sizeof_3 (h :: t) = sizeOf (h :: t)
    show 1 + sizeof_1 h + sizeof_3 t = 1 + sizeOf h + sizeOf t
    rw ih
    rfl

theorem Arg.val.sizeOf_spec [SizeOf α] (a : α) : sizeOf (Arg.val a) = 1 + sizeOf a :=
  rfl

theorem Arg.expr.sizeOf_spec [SizeOf α] (e : Expr α) : sizeOf (Arg.expr e) = 1 + sizeOf e :=
  rfl

theorem Expr.app.sizeOf_spec [SizeOf α] (f : String) (args : List (Arg α)) : sizeOf (Expr.app f args) = 1 + sizeOf f + sizeOf args := by
  show 1 + sizeOf f + sizeof_3 args = 1 + sizeOf f + sizeOf args
  rw aux_1

mutual
  inductive AList (α β : Type u)
    | nil
    | cons (a : α) (t : BList α β)

  inductive BList (α β : Type u)
    | cons (b : β) (t : AList α β)
end

namespace AList

noncomputable def sizeof_1 [SizeOf α] [SizeOf β] (a : AList α β) : Nat :=
  @AList.rec α β (fun _ => Nat) (fun _ => Nat)
    1
    (fun a _ ih => 1 + sizeOf a + ih)
    (fun b _ ih => 1 + sizeOf b + ih)
    a

noncomputable def sizeof_2 [SizeOf α] [SizeOf β] (a : BList α β) : Nat :=
  @BList.rec α β (fun _ => Nat) (fun _ => Nat)
    1
    (fun a _ ih => 1 + sizeOf a + ih)
    (fun b _ ih => 1 + sizeOf b + ih)
    a

noncomputable instance [SizeOf α] [SizeOf β] : SizeOf (AList α β) := ⟨sizeof_1⟩
noncomputable instance [SizeOf α] [SizeOf β] : SizeOf (BList α β) := ⟨sizeof_2⟩

end AList

theorem AList.nil.sizeOf_spec [SizeOf α] [SizeOf β] : sizeOf (AList.nil : AList α β) = 1 :=
  rfl

theorem AList.cons.sizeOf_spec [SizeOf α] [SizeOf β] (a : α) (t : BList α β) : sizeOf (AList.cons a t) = 1 + sizeOf a + sizeOf t :=
  rfl

theorem BList.cons.sizeOf_spec [SizeOf α] [SizeOf β] (b : β) (t : AList α β) : sizeOf (BList.cons a t) = 1 + sizeOf a + sizeOf t :=
  rfl

mutual
  inductive Foo (α : Type u)
    | mk (cs : AList (Foo α) (Boo α))

  inductive Boo (α : Type u)
    | mk (a : α) (cs : BList (Foo α) (Boo α))
end

#check @Foo.rec
#check @Foo.rec_1
#check @Foo.rec_2
#check @Boo.rec

namespace Foo

noncomputable def sizeof_1 [SizeOf α] (a : Foo α) : Nat :=
  @Foo.rec α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ ih => 1 + ih)
    (fun a _ ih => 1 + sizeOf a + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable def sizeof_2 [SizeOf α] (a : Boo α) : Nat :=
  @Boo.rec α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ ih => 1 + ih)
    (fun a _ ih => 1 + sizeOf a + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable def sizeof_3 [SizeOf α] (a : AList (Foo α) (Boo α)) : Nat :=
  @Foo.rec_1 α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ ih => 1 + ih)
    (fun a _ ih => 1 + sizeOf a + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable def sizeof_4 [SizeOf α] (a : BList (Foo α) (Boo α)) : Nat :=
  @Foo.rec_2 α (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ ih => 1 + ih)
    (fun a _ ih => 1 + sizeOf a + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    a

noncomputable instance [SizeOf α] : SizeOf (Foo α) := ⟨sizeof_1⟩
noncomputable instance [SizeOf α] : SizeOf (Boo α) := ⟨sizeof_2⟩

theorem aux_1 [SizeOf α] (a : AList (Foo α) (Boo α)) : sizeof_3 a = sizeOf a :=
  @AList.rec (Foo α) (Boo α) (fun a => sizeof_3 a = sizeOf a) (fun b => sizeof_4 b = sizeOf b)
    rfl
    (fun a t ih => by
      show sizeof_3 (AList.cons a t) = sizeOf (AList.cons a t)
      show 1 + sizeOf a + sizeof_4 t = sizeOf (AList.cons a t)
      rw ih
      rfl)
    (fun b t ih => by
      show sizeof_4 (BList.cons b t) = sizeOf (BList.cons b t)
      show 1 + sizeOf b + sizeof_3 t = sizeOf (BList.cons b t)
      rw ih
      rfl)
    a

theorem aux_2 [SizeOf α] (a : BList (Foo α) (Boo α)) : sizeof_4 a = sizeOf a :=
  @BList.rec (Foo α) (Boo α) (fun a => sizeof_3 a = sizeOf a) (fun b => sizeof_4 b = sizeOf b)
    rfl
    (fun a t ih => by
      show sizeof_3 (AList.cons a t) = sizeOf (AList.cons a t)
      show 1 + sizeOf a + sizeof_4 t = sizeOf (AList.cons a t)
      rw ih
      rfl)
    (fun b t ih => by
      show sizeof_4 (BList.cons b t) = sizeOf (BList.cons b t)
      show 1 + sizeOf b + sizeof_3 t = sizeOf (BList.cons b t)
      rw ih
      rfl)
    a

end Foo

theorem Foo.mk.sizeOf_spec [SizeOf α] (cs : AList (Foo α) (Boo α)) : sizeOf (Foo.mk cs) = 1 + sizeOf cs := by
  show 1 + Foo.sizeof_3 cs = 1 + sizeOf cs
  rw Foo.aux_1

theorem Boo.mk.sizeOf_spec [SizeOf α] (a : α) (cs : BList (Foo α) (Boo α)) : sizeOf (Boo.mk a cs) = 1 + sizeOf a + sizeOf cs := by
  show 1 + sizeOf a + Foo.sizeof_4 cs = 1 + sizeOf a + sizeOf cs
  rw Foo.aux_2

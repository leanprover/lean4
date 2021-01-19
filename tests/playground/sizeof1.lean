mutual

inductive TreePos (α : Type u) (β : Type v) where
  | leaf (a : α)
  | node (children : List (List (TreeNeg α β)))

inductive TreeNeg (α : Type u) (β : Type v) where
  | leaf (a : β)
  | node (children : List (List (TreePos α β)))

end

#check @TreePos.rec
#check @TreePos.rec_1
#check @TreePos.rec_2
#check @TreePos.rec_3
#check @TreePos.rec_4
#check @TreeNeg.rec

noncomputable def sizeof_1 [SizeOf α] [SizeOf β] (x : TreePos α β) : Nat :=
  @TreePos.rec α β (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun _ ih => 1 + ih)
    (fun b => 1 + sizeOf b)
    (fun _ ih => 1 + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    x

noncomputable def sizeof_2 [SizeOf α] [SizeOf β] (x : TreeNeg α β) : Nat :=
  @TreeNeg.rec α β (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun _ ih => 1 + ih)
    (fun b => 1 + sizeOf b)
    (fun _ ih => 1 + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    x

noncomputable def sizeof_3 [SizeOf α] [SizeOf β] (x : List (List (TreeNeg α β))) : Nat :=
  @TreePos.rec_1 α β (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun _ ih => 1 + ih)
    (fun b => 1 + sizeOf b)
    (fun _ ih => 1 + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    x

noncomputable def sizeof_4 [SizeOf α] [SizeOf β] (x : List (List (TreePos α β))) : Nat :=
  @TreePos.rec_2 α β (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun _ ih => 1 + ih)
    (fun b => 1 + sizeOf b)
    (fun _ ih => 1 + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    x

noncomputable def sizeof_5 [SizeOf α] [SizeOf β] (x : List (TreeNeg α β)) : Nat :=
  @TreePos.rec_3 α β (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun _ ih => 1 + ih)
    (fun b => 1 + sizeOf b)
    (fun _ ih => 1 + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    x

noncomputable def sizeof_6 [SizeOf α] [SizeOf β] (x : List (TreePos α β)) : Nat :=
  @TreePos.rec_4 α β (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun a => 1 + sizeOf a)
    (fun _ ih => 1 + ih)
    (fun b => 1 + sizeOf b)
    (fun _ ih => 1 + ih)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    1
    (fun _ _ ih₁ ih₂ => 1 + ih₁ + ih₂)
    x

noncomputable instance [SizeOf α] [SizeOf β] : SizeOf (TreePos α β) := ⟨sizeof_1⟩

noncomputable instance [SizeOf α] [SizeOf β] : SizeOf (TreeNeg α β) := ⟨sizeof_2⟩

theorem aux_1 [SizeOf α] [SizeOf β] (cs : List (TreePos α β)) : sizeof_6 cs = sizeOf cs :=
  @TreePos.rec_4 α β (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun cs => sizeof_6 cs = sizeOf cs)
    (fun a => trivial)
    (fun _ ih => trivial)
    (fun b => trivial)
    (fun _ ih => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    trivial
    (fun _ _ _ _ => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    rfl
    (fun h t ih₁ ih₂ => by
      show 1 + sizeof_1 h + sizeof_6 t = 1 + sizeOf h + sizeOf t
      rw ih₂
      rfl)
    cs

theorem aux_2 [SizeOf α] [SizeOf β] (cs : List (List (TreePos α β))) : sizeof_4 cs = sizeOf cs :=
  @TreePos.rec_2 α β (fun _ => True) (fun _ => True) (fun _ => True) (fun cs => sizeof_4 cs = sizeOf cs) (fun _ => True) (fun _ => True)
    (fun a => trivial)
    (fun _ ih => trivial)
    (fun b => trivial)
    (fun _ ih => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    rfl
    (fun h t ih₁ ih₂ => by
      show sizeof_4 (h::t) = sizeOf (h::t)
      show 1 + sizeof_6 h + sizeof_4 t = 1 + sizeOf h + sizeOf t
      rw ih₂
      rw aux_1)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    cs

theorem aux_3 [SizeOf α] [SizeOf β] (cs : List (TreeNeg α β)) : sizeof_5 cs = sizeOf cs :=
  @TreePos.rec_3 α β (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun cs => sizeof_5 cs = sizeOf cs) (fun _ => True)
    (fun a => trivial)
    (fun _ ih => trivial)
    (fun b => trivial)
    (fun _ ih => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    trivial
    (fun _ _ _ _ => trivial)
    rfl
    (fun h t ih₁ ih₂ => by
      show 1 + sizeof_2 h + sizeof_5 t = 1 + sizeOf h + sizeOf t
      rw ih₂
      rfl)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    cs

theorem aux_4 [SizeOf α] [SizeOf β] (cs : List (List (TreeNeg α β))) : sizeof_3 cs = sizeOf cs :=
  @TreePos.rec_1 α β (fun _ => True) (fun _ => True) (fun cs => sizeof_3 cs = sizeOf cs) (fun _ => True) (fun _ => True) (fun _ => True)
    (fun a => trivial)
    (fun _ ih => trivial)
    (fun b => trivial)
    (fun _ ih => trivial)
    rfl
    (fun h t ih₁ ih₂ => by
      show sizeof_3 (h::t) = sizeOf (h::t)
      show 1 + sizeof_5 h + sizeof_3 t = 1 + sizeOf h + sizeOf t
      rw ih₂
      rw aux_3)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    cs

theorem TreePos.leaf.sizeOf_spec [SizeOf α] [SizeOf β] (a : α) : sizeOf (TreePos.leaf (β := β) a) = 1 + sizeOf a :=
  rfl

theorem TreePos.node.sizeOf_spec [SizeOf α] [SizeOf β] (cs : List (List (TreeNeg α β))) : sizeOf (TreePos.node cs) = 1 + sizeOf cs := by
  show 1 + sizeof_3 cs = 1 + sizeOf cs
  rw aux_4

theorem TreeNeg.leaf.sizeOf_spec [SizeOf α] [SizeOf β] (b : β) : sizeOf (TreeNeg.leaf (α := α) b) = 1 + sizeOf b :=
  rfl

theorem TreeNeg.node.sizeOf_spec [SizeOf α] [SizeOf β] (cs : List (List (TreePos α β))) : sizeOf (TreeNeg.node cs) = 1 + sizeOf cs := by
  show 1 + sizeof_4 cs = 1 + sizeOf cs
  rw aux_2

mutual

inductive TreePos (α : Type u) (β : Type v) where
  | leaf (a : α)
  | node (children : List (List (TreeNeg α β)))

inductive TreeNeg (α : Type u) (β : Type v) where
  | leaf (a : β)
  | node (children : List (List (TreePos α β)))

end

theorem aux_1 [SizeOf α] [SizeOf β] (cs : List (TreePos α β)) : TreePos._sizeOf_6 cs = sizeOf cs :=
  @TreePos.rec_4 α β (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun cs => TreePos._sizeOf_6 cs = sizeOf cs)
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
      show 1 + TreePos._sizeOf_1 h + TreePos._sizeOf_6 t = sizeOf (h::t)
      rw ih₂
      rfl)
    cs

theorem aux_2 [SizeOf α] [SizeOf β] (cs : List (List (TreePos α β))) : TreePos._sizeOf_4 cs = sizeOf cs :=
  @TreePos.rec_2 α β (fun _ => True) (fun _ => True) (fun _ => True) (fun cs => TreePos._sizeOf_4 cs = sizeOf cs) (fun _ => True) (fun _ => True)
    (fun a => trivial)
    (fun _ ih => trivial)
    (fun b => trivial)
    (fun _ ih => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    rfl
    (fun h t ih₁ ih₂ => by
      show 1 + TreePos._sizeOf_6 h + TreePos._sizeOf_4 t = sizeOf (h :: t)
      rw ih₂
      rw aux_1
      rfl)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    cs

theorem aux_3 [SizeOf α] [SizeOf β] (cs : List (TreeNeg α β)) : TreePos._sizeOf_5 cs = sizeOf cs :=
  @TreePos.rec_3 α β (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun cs => TreePos._sizeOf_5 cs = sizeOf cs) (fun _ => True)
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
      show 1 + TreePos._sizeOf_2 h + TreePos._sizeOf_5 t = sizeOf (h::t)
      rw ih₂
      rfl)
    trivial
    (fun _ _ ih₁ ih₂ => trivial)
    cs

theorem aux_4 [SizeOf α] [SizeOf β] (cs : List (List (TreeNeg α β))) : TreePos._sizeOf_3 cs = sizeOf cs :=
  @TreePos.rec_1 α β (fun _ => True) (fun _ => True) (fun cs => TreePos._sizeOf_3 cs = sizeOf cs) (fun _ => True) (fun _ => True) (fun _ => True)
    (fun a => trivial)
    (fun _ ih => trivial)
    (fun b => trivial)
    (fun _ ih => trivial)
    rfl
    (fun h t ih₁ ih₂ => by
      show 1 + TreePos._sizeOf_5 h + TreePos._sizeOf_3 t = sizeOf (h :: t)
      rw ih₂
      rw aux_3
      rfl)
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
  show 1 + TreePos._sizeOf_3 cs = 1 + sizeOf cs
  rw aux_4

theorem TreeNeg.leaf.sizeOf_spec [SizeOf α] [SizeOf β] (b : β) : sizeOf (TreeNeg.leaf (α := α) b) = 1 + sizeOf b :=
  rfl

theorem TreeNeg.node.sizeOf_spec [SizeOf α] [SizeOf β] (cs : List (List (TreePos α β))) : sizeOf (TreeNeg.node cs) = 1 + sizeOf cs := by
  show 1 + TreePos._sizeOf_4 cs = 1 + sizeOf cs
  rw aux_2

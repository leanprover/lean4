mutual
  inductive AList (α β : Type u)
    | nil
    | cons (a : α) (t : BList α β)

  inductive BList (α β : Type u)
    | cons (b : β) (t : AList α β)
end

namespace AList


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

namespace Foo

theorem aux_1 [SizeOf α] (a : AList (Foo α) (Boo α)) : Foo._sizeOf_3 a = sizeOf a :=
  @AList.rec (Foo α) (Boo α) (fun a => Foo._sizeOf_3 a = sizeOf a) (fun b => Foo._sizeOf_4 b = sizeOf b)
    rfl
    (fun a t ih => by
      show 1 + sizeOf a + Foo._sizeOf_4 t = sizeOf (AList.cons a t)
      rw ih
      rfl)
    (fun b t ih => by
      show 1 + sizeOf b + Foo._sizeOf_3 t = sizeOf (BList.cons b t)
      rw ih
      rfl)
    a

theorem aux_2 [SizeOf α] (a : BList (Foo α) (Boo α)) : Foo._sizeOf_4 a = sizeOf a :=
  @BList.rec (Foo α) (Boo α) (fun a => Foo._sizeOf_3 a = sizeOf a) (fun b => Foo._sizeOf_4 b = sizeOf b)
    rfl
    (fun a t ih => by
      show 1 + sizeOf a + Foo._sizeOf_4 t = sizeOf (AList.cons a t)
      rw ih
      rfl)
    (fun b t ih => by
      show 1 + sizeOf b + Foo._sizeOf_3 t = sizeOf (BList.cons b t)
      rw ih
      rfl)
    a

end Foo

theorem Foo.mk.sizeOf_spec [SizeOf α] (cs : AList (Foo α) (Boo α)) : sizeOf (Foo.mk cs) = 1 + sizeOf cs := by
  show 1 + Foo._sizeOf_3 cs = 1 + sizeOf cs
  rw Foo.aux_1

theorem Boo.mk.sizeOf_spec [SizeOf α] (a : α) (cs : BList (Foo α) (Boo α)) : sizeOf (Boo.mk a cs) = 1 + sizeOf a + sizeOf cs := by
  show 1 + sizeOf a + Foo._sizeOf_4 cs = 1 + sizeOf a + sizeOf cs
  rw Foo.aux_2

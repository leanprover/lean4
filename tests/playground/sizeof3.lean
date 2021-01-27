set_option trace.Meta.sizeOf true in
mutual
  inductive AList (α β : Type u)
    | nil
    | cons (a : α) (t : BList α β)

  inductive BList (α β : Type u)
    | cons (b : β) (t : AList α β)
end

#print AList.nil.sizeOf_spec
#print AList.cons.sizeOf_spec
#print BList.cons.sizeOf_spec

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

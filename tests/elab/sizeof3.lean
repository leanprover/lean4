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

#print Boo.mk.sizeOf_spec
#print Foo._sizeOf_4_eq
#print Foo._sizeOf_3_eq

def prod.cmp (a b : nat × nat) : ordering :=
cmp a b

namespace prod
  def foo (a : nat × nat) (cmp : nat) :=
  a.cmp
end prod

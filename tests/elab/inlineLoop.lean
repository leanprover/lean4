namespace Test1
mutual

  partial def f (a : Nat) : Nat := g a

  partial def g (a : Nat) : Nat := f a

end
end Test1

namespace Test2
mutual

  @[inline]
  partial def f (a : Nat) : Nat := g a + g a + g a + g a

  @[inline]
  partial def g (a : Nat) : Nat := f a + f a + f a + f a

end
end Test2

namespace Test3

partial def unsafeFn1 {m} [Monad m] (a : α)  : m α :=
  unsafeFn1 a

end Test3

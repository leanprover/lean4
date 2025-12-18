universe u

inductive Foo : Type u → Type u → Type (u+1)
  | foo {as bs cs: Type u}: Foo as bs → Foo bs cs → Foo as cs

namespace Foo
  mutual
    def bar    : {as bs: Type u} → Foo.{u} as bs → bs :=
      bar_aux
    termination_by _ _ => 0
    decreasing_by sorry

    def bar_aux: {as bs: Type u} → Foo.{u} as bs → bs
      | as, bs, foo _ x => x.bar
    termination_by _ _ _ => 0
    decreasing_by sorry

  end
end Foo


namespace Foo
  mutual
    def bar1    : {as bs: Type u} → Foo.{u} as bs → bs
      | as, bs, x => bar_aux1 x
    termination_by _ _ _ => 0
    decreasing_by sorry

    def bar_aux1 : {as bs: Type u} → Foo.{u} as bs → bs
      | as, bs, foo _ x => x.bar1
    termination_by _ _ _ => 0
    decreasing_by sorry

  end
end Foo


namespace Foo
  mutual
    def bar2    : Foo as bs → bs
      | x => bar_aux2 x
  termination_by x => (sizeOf x, 1)

    def bar_aux2 : Foo as bs → bs
      | foo _ x => x.bar2
  termination_by x => (sizeOf x, 0)

  end
end Foo

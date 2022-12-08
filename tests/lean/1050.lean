universe u

inductive Foo : Type u → Type u → Type (u+1)
  | foo {as bs cs: Type u}: Foo as bs → Foo bs cs → Foo as cs

namespace Foo
  mutual
    def bar    : {as bs: Type u} → Foo.{u} as bs → bs :=
      bar_aux

    def bar_aux: {as bs: Type u} → Foo.{u} as bs → bs
      | as, bs, foo _ x => x.bar

  end
  termination_by
    bar     => 0
    bar_aux => 0
  decreasing_by sorry
end Foo


namespace Foo
  mutual
    def bar1    : {as bs: Type u} → Foo.{u} as bs → bs
      | as, bs, x => bar_aux1 x

    def bar_aux1 : {as bs: Type u} → Foo.{u} as bs → bs
      | as, bs, foo _ x => x.bar1

  end
  termination_by
    bar1     => 0
    bar_aux1 => 0
  decreasing_by sorry
end Foo


namespace Foo
  mutual
    def bar2    : Foo as bs → bs
      | x => bar_aux2 x

    def bar_aux2 : Foo as bs → bs
      | foo _ x => x.bar2

  end
  termination_by
    bar2     x => (sizeOf x, 1)
    bar_aux2 x => (sizeOf x, 0)
end Foo

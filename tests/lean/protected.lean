

namespace Foo

protected def x := 10

end Foo

open Foo
#check x -- error unknown identifier `x`

#check Foo.x

namespace Bla.Foo
protected def y := 20
def z := 30
end Bla.Foo

open Bla
#check Foo.y
open Bla.Foo
#check y -- error unknown identifier `y`
#check z

protected def x := 0  -- Error

protected partial def Foo.f (x : Nat) :=
if x > 0 then f (x-1) * 2 else 1 -- Error

protected partial def Bla.f (x : Nat) :=
if x > 0 then Bla.f (x-1) * 2 else 1

#eval Bla.f 3

namespace Foo

protected partial def g (x : Nat) :=
if x > 0 then g (x-1) * 2 else 1 -- error

end Foo

namespace Bla

protected partial def g (x : Nat) :=
if x > 0 then Bla.g (x-1) * 2 else 1

#eval g 3 -- error

#eval Bla.g 3

end Bla


def S (σ : Type) (m : Type → Type) (α : Type) :=
σ → m (α × σ)

namespace S
variable {σ : Type} {m : Type → Type} [Monad m] {α : Type}

protected def pure (a : α) : S σ m α :=
fun s => pure (a, s) -- This `pure` is the top-level one. The `pure` being defined here is called `S.pure`.

end S

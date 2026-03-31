def foo : Inhabited Nat :=
  set_option trace.Meta.synthInstance true in by { exact inferInstance }

namespace Foo
  def bla := 20
end Foo

def boo : Nat :=
  open Foo in by exact bla

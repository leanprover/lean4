namespace Foo

def f (n : Nat) : Bool :=
  n == 0

end Foo

namespace Boo

def f (n : String) : String :=
  n ++ n

end Boo

open Foo
open Boo

def g := fun x => (f x : Bool)
                 --^ textDocument/hover
def h := fun x => (f x : String)
                 --^ textDocument/hover

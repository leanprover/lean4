private def blaBlaBoo := 2

#check blaB
         --^ textDocument/completion

namespace Foo

private def booBoo := 3

#check booB
         --^ textDocument/completion

end Foo

structure S where
  field1 : Nat

private def S.getInc (s : S) : Nat :=
  s.field1 + 1

def tst1 (s : S) : Nat :=
  s.g
   --^ textDocument/completion

def tst2 (s : S) : Nat :=
  s.
  --^ textDocument/completion

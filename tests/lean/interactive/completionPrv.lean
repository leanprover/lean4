private def longAndHopefullyUniqueBlaBlaBoo := 2

#check longAndHopefullyUniqueBlaB
                               --^ completion

namespace Foo

private def longAndHopefullyUniqueBooBoo := 3

#check longAndHopefullyUniqueBooB
                               --^ completion

end Foo

structure S where
  field1 : Nat

private def S.getInc (s : S) : Nat :=
  s.field1 + 1

def tst1 (s : S) : Nat :=
  s.g
   --^ completion

def tst2 (s : S) : Nat :=
  s.
  --^ completion

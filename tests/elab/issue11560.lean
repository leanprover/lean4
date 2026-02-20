structure Fin' (n : Nat) where
  mk ::
  val  : Nat
  isLt : LT.lt val n

example
 (a b c d : Nat)
 (h1 : c.succ < a)
 (h2 : d.succ < b)
 (hab : a = b)
 (hcd : @Fin'.mk a c.succ h1 ≍ @Fin'.mk b d.succ h2) :
 c = d := Fin'.noConfusion hab hcd (fun h => Nat.succ.noConfusion h fun h' => h')

example
 (a b c d : Nat)
 (h1 : c.succ < a)
 (h2 : d.succ < b)
 (hab : a = b)
 (hcd : @Fin'.mk a c.succ h1 ≍ @Fin'.mk b d.succ h2) :
 c = d := by
  grind

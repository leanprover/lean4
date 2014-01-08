variable p : Nat -> Nat -> Bool
check fun (a b c : Bool) (p : Nat -> Nat -> Bool) (n m : Nat)
          (H : a → b → (forall x y, c → p (x + n) (x + m)))
          (Ha : a)
          (Hb : b)
          (Hc : c),
          H Ha Hb 0 1 Hc

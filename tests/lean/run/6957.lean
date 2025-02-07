/-!
casesOn reduction works properly even when applied to a constructor of a
different type with a compatible representation.
-/
unsafe def test : Nat :=
  Subtype.casesOn (unsafeCast () : { x : Unit // x = x }) (fun _ _ => 0)

variable (a : true = true → Bool)

example : (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _) = fun h => a h := rfl
example : (fun h => a h) = a := rfl
example  : (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _) = a := rfl

variable (a : Unit → Bool)
example : @PUnit.rec (fun _ => Bool) (a ()) = a := rfl--fails

variable (a : Bool × Bool → Bool)
example : @Prod.rec Bool Bool (motive := fun _ => Bool) (fun b c => a (b,c)) = fun b => a b := rfl --works
example : @Prod.rec Bool Bool (motive := fun _ => Bool) (fun b c => a (b,c)) = a := rfl --fails

-- This should probably be filed as another issue since it is about allowing for eta-expansion when checking defeq against a partial structure constructor application, not against a partially applied recursor
-- structure T where
  -- val : Bool
  -- proof : True
--
-- variable (x : True → T)
-- #check T.mk (x True.intro).val
-- example : (T.mk (x True.intro).val) = (fun h => x h) := rfl
-- example : (fun h => x h) = x := rfl
-- example : (T.mk (x True.intro).val) = x := rfl

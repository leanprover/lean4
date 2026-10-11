/-! Ensures partial applications of recursors for K-like and structure types are appropriately eta-expanded during type-checking.-/

variable (a : true = true → Bool)

example : (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _) = fun h => a h := rfl
example : (fun h => a h) = a := rfl
example  : (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _) = a := rfl

variable (a : Unit → Bool)
example : @PUnit.rec (fun _ => Bool) (a ()) = a := rfl

variable (a : Bool × Bool → Bool)
example : @Prod.rec Bool Bool (motive := fun _ => Bool) (fun b c => a (b,c)) = fun b => a b := rfl
example : @Prod.rec Bool Bool (motive := fun _ => Bool) (fun b c => a (b,c)) = a := rfl

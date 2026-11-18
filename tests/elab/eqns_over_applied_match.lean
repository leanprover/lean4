/-!
Equation lemmas split a `match` that is applied to more arguments than its arity, also when an
alternative needs an overlap hypothesis.
-/

def over (a b : Bool) (n : Nat) : Nat :=
  (match a, b with
    | true, true => fun n => n
    | _, _ => fun _ => 0) n

/--
info: over.eq_1 (n : Nat) : over true true n = n
-/
#guard_msgs in
#check over.eq_1

/--
info: over.eq_2 (a b : Bool) (n : Nat) (x_2 : a = true → b = true → False) : over a b n = (fun x => 0) n
-/
#guard_msgs in
#check over.eq_2

inductive WT where
  | of : Nat → WT
  | star : WT

@[reducible] def WT.Hom : WT → WT → Type
  | of _, of _ => Nat
  | star, of _ => PEmpty
  | _, star => PUnit

/-- The over-applied `match` that `@[to_dual]` produces for a composition of morphisms. -/
def WT.comp {X Y Z : WT} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  (match (motive := (x y z : WT) → Hom x y → Hom y z → Hom x z) X, Y, Z with
    | of _, of _, of _ => fun f g => (f + g : Nat)
    | of _, _, star => fun _ _ => PUnit.unit
    | star, of _, _ => fun f _ => PEmpty.elim f
    | _, star, of _ => fun _ g => PEmpty.elim g
    | star, star, star => fun _ _ => PUnit.unit) f g

/-- info: WT.comp.eq_5 (f g : WT.star.Hom WT.star) : WT.comp f g = PUnit.unit -/
#guard_msgs in
#check WT.comp.eq_5

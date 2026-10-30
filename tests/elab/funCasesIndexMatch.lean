inductive W where | a | b

inductive Op : W → Type where
  | y : Fin w.ctorIdx → Op w

def Op.f {w} (i : Op w) : Nat :=
  match (generalizing := false) (motive := Op w → Nat) i with
  | .y _ =>
    match (generalizing := false) (motive := W → Nat) w with
    | .a => 1
    | _ => 2

/--
info: Op.f.fun_cases_unfolding (motive : {w : W} → Op w → Nat → Prop) (case1 : ∀ (a : Fin W.a.ctorIdx), motive (Op.y a) 1)
  (case2 : ∀ {w : W} (a : Fin w.ctorIdx), (w = W.a → False) → motive (Op.y a) 2) {w : W} (i : Op w) : motive i i.f
-/
#guard_msgs in
#check Op.f.fun_cases_unfolding

/--
info: Op.f.fun_cases (motive : {w : W} → Op w → Prop) (case1 : ∀ (a : Fin W.a.ctorIdx), motive (Op.y a))
  (case2 : ∀ {w : W} (a : Fin w.ctorIdx), (w = W.a → False) → motive (Op.y a)) {w : W} (i : Op w) : motive i
-/
#guard_msgs in
#check Op.f.fun_cases

example {w} (i : Op w) : i.f ≤ 2 := by
  fun_cases Op.f i <;> simp

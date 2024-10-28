inductive Many (α : Type u) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def many_map {α β : Type} (f : α → β) : Many α → Many β
  | .none => .none
  | .more x xs => Many.more (f x) (fun () => many_map f <| xs ())

/--
info: many_map.induct {α β : Type} (f : α → β) (motive : Many α → Prop) (case1 : motive Many.none)
  (case2 : ∀ (x : α) (xs : Unit → Many α), motive (xs ()) → motive (Many.more x xs)) (a✝ : Many α) : motive a✝
-/
#guard_msgs in
#check many_map.induct

-- Unrelated, but for fun, show that we get the identical theorem from well-founded recursion

def many_map' {α β : Type} (f : α → β) : Many α → Many β
  | .none => .none
  | .more x xs => Many.more (f x) (fun () => many_map' f <| xs ())
termination_by m => m

example : @many_map.induct = @many_map'.induct := rfl

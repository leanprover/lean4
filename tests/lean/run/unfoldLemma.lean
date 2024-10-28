def Option_map (f : α → β) : Option α → Option β
  | none => none
  | some x => some (f x)

/--
info: equations:
theorem Option_map.eq_1.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β), Option_map f none = none
theorem Option_map.eq_2.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x_1 : α),
  Option_map f (some x_1) = some (f x_1)
-/
#guard_msgs in
#print equations Option_map

/--
info: Option_map.eq_def.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) (x✝ : Option α) :
  Option_map f x✝ =
    match x✝ with
    | none => none
    | some x => some (f x)
-/
#guard_msgs in
#check Option_map.eq_def

/--
info: Option_map.eq_unfold.{u_1, u_2} :
  @Option_map = fun {α} {β} f x =>
    match x with
    | none => none
    | some x => some (f x)
-/
#guard_msgs in
#check Option_map.eq_unfold

def answer := 42

/-- info: answer.eq_unfold : answer = 42 -/
#guard_msgs in
#check answer.eq_unfold

-- structural recursion
def List_map (f : α → β) : List α → List β
  | [] => []
  | x::xs => f x :: List_map f xs
/--
info: List_map.eq_unfold.{u_1, u_2} :
  @List_map = fun {α} {β} f x =>
    match x with
    | [] => []
    | x :: xs => f x :: List_map f xs
-/
#guard_msgs in
#check List_map.eq_unfold

-- wf recursion
def List_map2 (f : α → β) : List α → List β
  | [] => []
  | x::xs => f x :: List_map2 f xs
termination_by l => l

/--
info: List_map2.eq_unfold.{u_1, u_2} :
  @List_map2 = fun {α} {β} f x =>
    match x with
    | [] => []
    | x :: xs => f x :: List_map2 f xs
-/
#guard_msgs in
#check List_map2.eq_unfold

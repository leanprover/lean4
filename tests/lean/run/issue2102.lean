-- works
def g' (T : Type) (ls : List T) : (Option (List T)) :=
  match ls with
  | _::tl =>
      let res := Option.attach (g' T tl)
      res.bind fun x => x.val
  | [] => .none

-- doesn't

/--
error: fail to show termination for
  g''
with errors
failed to infer structural recursion:
Not considering parameter T of g'':
  its type is not an inductive
Not considering parameter ls of g'':
  its type is an inductive datatype
    List T
  and the datatype parameter
    T
  depends on the function parameter
    T
  which is not fixed.
no parameters suitable for structural recursion

failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
T✝ : Type
head✝ : T✝
tl : List T✝
T : Type
ls : List T
⊢ sizeOf ls < 1 + sizeOf tl
-/
#guard_msgs in
def g'' (T : Type) (ls : List T) : (Option (List T)) :=
  match ls with
  | _::tl =>
      let res := Option.attach (g'' T tl)
      res.bind fun ⟨x,h⟩ => x
  | [] => .none

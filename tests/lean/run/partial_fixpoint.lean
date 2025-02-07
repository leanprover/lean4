def monadic (x : Nat) : Option Unit := monadic (x + 1)
partial_fixpoint

def loop (x : Nat) : Unit := loop (x + 1)
partial_fixpoint

def monadic0 : Option Unit := monadic0
partial_fixpoint

def loop0 : Unit := loop0
partial_fixpoint


/--
info: equations:
theorem loop.eq_1 : ∀ (x : Nat), loop x = loop (x + 1)
-/
#guard_msgs in
#print equations loop

/-- error: unknown constant 'loop.induct' -/
#guard_msgs in
#check loop.induct

def find (P : Nat → Bool) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    find P (x +1)
partial_fixpoint

/--
info: equations:
theorem find.eq_1 : ∀ (P : Nat → Bool) (x : Nat), find P x = if P x = true then some x else find P (x + 1)
-/
#guard_msgs in
#print equations find

/--
error: failed to compile definition 'notinhabited' using `partial_fixpoint`, could not prove that the type
  (n : Nat) → Nat → Fin n
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
def notinhabited (n m : Nat) : Fin n :=
  notinhabited n (m+1)
partial_fixpoint

/--
error: failed to compile definition 'notinhabited_mutual1' using `partial_fixpoint`, could not prove that the type
  (n : Nat) → Nat → Fin n
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
mutual
def notinhabited_mutual1 (n m : Nat) : Fin n :=
  notinhabited_mutual2 n (m+1)
partial_fixpoint
def notinhabited_mutual2 (n m : Nat) : Fin n :=
  notinhabited_mutual1 n (m+1)
partial_fixpoint
end


/--
error: Could not prove 'notTailRec1' to be monotone in its recursive calls:
  Cannot eliminate recursive call `notTailRec1 (n + 1)` enclosed in
    notTailRec1 (n + 1) - 1
-/
#guard_msgs in
def notTailRec1 (n : Nat) := notTailRec1 (n + 1) - 1
partial_fixpoint

/--
error: Could not prove 'notTailRec2' to be monotone in its recursive calls:
  Cannot eliminate recursive call `notTailRec2 n (m + 1)` enclosed in
    notTailRec2 n (m + 1) - 1
-/
#guard_msgs in
def notTailRec2 (n m : Nat) := notTailRec2 n (m + 1) - 1
partial_fixpoint

/--
error: Could not prove 'notTailRec3' to be monotone in its recursive calls:
  Cannot eliminate recursive call `notTailRec3 (m + 1) n` enclosed in
    notTailRec3 (m + 1) n - 1
-/
#guard_msgs in
def notTailRec3 (n m : Nat) := notTailRec3 (m + 1) n - 1
partial_fixpoint

/--
error: Could not prove 'notTailRec4a' to be monotone in its recursive calls:
  Cannot eliminate recursive call `notTailRec4b (m + 1) n` enclosed in
    notTailRec4b (m + 1) n - 1
-/
#guard_msgs in
mutual
def notTailRec4a (n m : Nat) := notTailRec4b (m + 1) n - 1
partial_fixpoint
def notTailRec4b (n m : Nat) := notTailRec4a (m + 1) n - 1
partial_fixpoint
end

def fib (n : Nat) := go 0 0 1
where
  go i fip fi :=
    if i = n then
      fi
    else
      go (i + 1) fi (fi + fip)
  partial_fixpoint

local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (if b then α else β) := by
  split <;> assumption

def dependent1 (b : Bool) (n : Nat) : if b then Nat else Bool
  := dependent1 b (n + 1)
partial_fixpoint

def dependent2 (b : Bool) (n : Nat) : if b then Nat else Bool :=
  if b then dependent2 b (n + 1) else dependent2 b (n + 1)
partial_fixpoint

def dependent2' (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if b then dependent2' (n + 1) b else dependent2' (n + 2) b
partial_fixpoint

def dependent2'' (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2'' (n + 1) b else dependent2'' (n + 2) b
partial_fixpoint

local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (cond b α β) := by
  cases b <;> assumption

def dependent3 (b : Bool) (n : Nat) : cond b Nat Bool :=
  match b with
  | true => dependent3 true (n + 1)
  | false => dependent3 false (n + 2)
partial_fixpoint

mutual
def mutualUnary1 (n : Nat) : Unit := mutualUnary2 (n + 1)
partial_fixpoint
def mutualUnary2 (n : Nat) : Unit := mutualUnary1 (n + 1)
partial_fixpoint
end

mutual
def mutual1 (n m : Nat) : Unit := mutual2 (m + 1) n
partial_fixpoint
def mutual2 (n m : Nat) : Unit := mutual1 (m + 1) n
partial_fixpoint
end

mutual
def dependent2''a (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2''a (n + 1) b else dependent2''b (n + 2) b
partial_fixpoint
def dependent2''b (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2''a (n + 1) b else dependent2''b (n + 2) b
partial_fixpoint
end

/--
info: equations:
theorem dependent2''b.eq_1 : ∀ (n : Nat) (b : Bool),
  dependent2''b n b = if x : b = true then dependent2''a (n + 1) b else dependent2''b (n + 2) b
-/
#guard_msgs in #print equations dependent2''b

/--
info: dependent2''b.eq_unfold :
  dependent2''b = fun n b => if x : b = true then dependent2''a (n + 1) b else dependent2''b (n + 2) b
-/
#guard_msgs in #check dependent2''b.eq_unfold

def computeLfp' {α : Type u} [DecidableEq α] (f : α → α) (x : α) : α :=
  let next := f x
  if x ≠ next then
    computeLfp' f next
  else
    x
partial_fixpoint

/--
info: equations:
theorem computeLfp'.eq_1.{u} : ∀ {α : Type u} [inst : DecidableEq α] (f : α → α) (x : α),
  computeLfp' f x = if x ≠ f x then computeLfp' f (f x) else x
-/
#guard_msgs in #print equations computeLfp'

/--
error: Could not prove 'computeLfp'''' to be monotone in its recursive calls:
  Cannot eliminate recursive call `computeLfp''' f next` enclosed in
    id (computeLfp''' f next)
-/
#guard_msgs in
def computeLfp''' {α : Type u} [DecidableEq α] (f : α → α) (x : α) : α :=
  have next := f x
  if x ≠ next then
    id $ computeLfp''' f next -- NB: Error message should use correct variable name
  else
    x
partial_fixpoint

def whileSome (f : α → Option α) (x : α) : α :=
  match f x with
  | none => x
  | some x' => whileSome f x'
partial_fixpoint

/--
info: equations:
theorem whileSome.eq_1.{u_1} : ∀ {α : Type u_1} (f : α → Option α) (x : α),
  whileSome f x =
    match f x with
    | none => x
    | some x' => whileSome f x'
-/
#guard_msgs in #print equations whileSome

def ack : (n m : Nat) → Option Nat
  | 0,   y   => some (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint

/--
info: equations:
theorem ack.eq_1 : ∀ (x : Nat), ack 0 x = some (x + 1)
theorem ack.eq_2 : ∀ (x_2 : Nat), ack x_2.succ 0 = ack x_2 1
theorem ack.eq_3 : ∀ (x_2 y : Nat),
  ack x_2.succ y.succ = do
    let __do_lift ← ack (x_2 + 1) y
    ack x_2 __do_lift
-/
#guard_msgs in #print equations ack

/--
info: ack.eq_def (x✝ x✝¹ : Nat) :
  ack x✝ x✝¹ =
    match x✝, x✝¹ with
    | 0, y => some (y + 1)
    | x.succ, 0 => ack x 1
    | x.succ, y.succ => do
      let __do_lift ← ack (x + 1) y
      ack x __do_lift
-/
#guard_msgs in #check ack.eq_def

/--
info: ack.eq_unfold :
  ack = fun x x_1 =>
    match x, x_1 with
    | 0, y => some (y + 1)
    | x.succ, 0 => ack x 1
    | x.succ, y.succ => do
      let __do_lift ← ack (x + 1) y
      ack x __do_lift
-/
#guard_msgs in #check ack.eq_unfold

/--
error: Could not prove 'WrongMonad.ack' to be monotone in its recursive calls:
  Cannot eliminate recursive call `ack (x + 1) y` enclosed in
    do
      let __do_lift ← ack (x✝ + 1) y✝
      ack x✝ __do_lift
  Tried to apply 'Lean.Order.monotone_bind', but failed.
  Possible cause: A missing `Lean.Order.MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
-/
#guard_msgs in
def WrongMonad.ack : (n m : Nat) → Id Nat
  | 0,   y   => pure (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint

structure Tree where cs : List Tree

def Tree.rev (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (Tree.rev ·))
partial_fixpoint

def Tree.rev' (t : Tree) : Option Tree := do
  let mut cs := []
  for c in t.cs do
    cs := (← c.rev') :: cs
  return Tree.mk cs
partial_fixpoint



-- These tests check that the user's variable names are preserved in the goals

/--
error: Could not prove 'VarName.computeLfp' to be monotone in its recursive calls:
  Cannot eliminate recursive call `computeLfp f next` enclosed in
    id (computeLfp f next)
-/
#guard_msgs in
def VarName.computeLfp {α : Type u} [DecidableEq α] (f : α → Option α) (x : α) : Option α := do
  let next ← f x
  if x ≠ next then
    id $ computeLfp f next --NB: Error message should use correct variable name
  else
    x
partial_fixpoint


opaque mentionsH : ¬ b → α → α := fun _ x => x

/--
error: Could not prove 'VarName.dite' to be monotone in its recursive calls:
  Cannot eliminate recursive call `dite (n + 2) b` enclosed in
    mentionsH this_is_my_h (dite (n + 2) b)
-/
#guard_msgs in
def VarName.dite (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if this_is_my_h : b then dite (n + 1) b else mentionsH this_is_my_h (dite (n + 2) b)
partial_fixpoint


/--
error: Could not prove 'Tree.rev_bad' to be monotone in its recursive calls:
  Cannot eliminate recursive call `Tree.rev_bad my_name` enclosed in
    id my_name.rev_bad
-/
#guard_msgs in
def Tree.rev_bad (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (fun my_name => id (Tree.rev_bad my_name)))
partial_fixpoint

/--
error: Could not prove 'Tree.rev''' to be monotone in its recursive calls:
  Cannot eliminate recursive call `Tree.rev'' my_name` enclosed in
    id (if my_idx < 0 then some my_name else my_name.rev'')
-/
#guard_msgs in
def Tree.rev'' (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.toArray.mapFinIdxM
    (fun my_idx my_name _ => id (if my_idx < 0 then my_name else Tree.rev'' my_name))).toList
partial_fixpoint

/--
error: Could not prove 'Tree.rev'''' to be monotone in its recursive calls:
  Cannot eliminate recursive call `Tree.rev''' my_tree.cs.toArray` enclosed in
    ts.reverse.mapFinIdxM fun my_idx my_tree x =>
      id
        (if my_idx < 0 then my_tree
        else do
          let ts ← rev''' my_tree.cs.toArray
          { cs := ts.toList })
  Tried to apply 'Lean.Order.Array.monotone_mapFinIdxM', but failed.
  Possible cause: A missing `Lean.Order.MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
-/
#guard_msgs in
def Tree.rev''' (ts : Array Tree) : Id (Array Tree) := do
  ts.reverse.mapFinIdxM
    (fun my_idx my_tree _ => id (if my_idx < 0 then my_tree else (Tree.rev''' my_tree.cs.toArray) >>= (fun ts => ⟨ts.toList⟩)))
partial_fixpoint

def List.findIndex (xs : List α) (p : α → Bool) : Option Nat := match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint


-- Applicative operator idioms

def app (n m : Nat) : Option Nat := (· + ·) <$> app (n - 1) m <*> app n (m - 1)
partial_fixpoint

def app' (n m : Nat) : Option Nat := pure (· + ·) <*> app' (n - 1) m <*> app' n (m - 1)
partial_fixpoint

def app'' {α} (n : Nat) : Option (α → α) := do
  let _n ← app'' (n+1) <*> pure 5
  pure id
partial_fixpoint

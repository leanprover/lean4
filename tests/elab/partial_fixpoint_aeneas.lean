/-!
Examples of partial functions taken from
https://github.com/AeneasVerif/aeneas/blob/9d3febaff93ff02756c648561c9ad2b18d5d9b62/backends/lean/Base/Diverge/Elab.lean
and using Option instead of Result
-/

abbrev Result := Option
abbrev Result.ok := @Option.some

def list_nth {a: Type u} (ls : List a) (i : Int) : Option a :=
    match ls with
    | [] => none
    | x :: ls => do
      if i = 0 then pure x
      else pure (← list_nth ls (i - 1))
partial_fixpoint

def list_nth_with_back {a: Type} (ls : List a) (i : Int) :
    Result (a × (a → Result (List a))) :=
    match ls with
    | [] => none
    | x :: ls =>
      if i = 0 then return (x, (λ ret => return (ret :: ls)))
      else do
        let (x, back) ← list_nth_with_back ls (i - 1)
        return (x,
          (λ ret => do
           let ls ← back ret
           return (x :: ls)))
partial_fixpoint


mutual
  def is_even (i : Int) : Result Bool :=
    if i = 0 then return true else return (← is_odd (i - 1))
  partial_fixpoint

  def is_odd (i : Int) : Result Bool :=
    if i = 0 then return false else return (← is_even (i - 1))
  partial_fixpoint
end

mutual
  def foo (i : Int) : Result Nat :=
      if i > 10 then return (← foo (i / 10)) + (← bar i) else bar 10
  partial_fixpoint

  def bar (i : Int) : Result Nat :=
      if i > 20 then foo (i / 20) else .ok 42
  partial_fixpoint
end

def test1 (_ : Option Bool) (_ : Unit) : Result Unit
    := test1 Option.none ()
partial_fixpoint

def infinite_loop : Result Unit := do
  let _ ← infinite_loop
  Result.ok ()
partial_fixpoint

def infinite_loop1 : Result Unit :=
  infinite_loop1
partial_fixpoint

section HigherOrder
  inductive Tree (a : Type u) where
  | leaf (x : a)
  | node (tl : List (Tree a))

def Tree.id {a : Type u} (t : Tree a) : Result (Tree a) :=
  match t with
  | .leaf x => .ok (.leaf x)
  | .node tl =>
    do
      let tl ← List.mapM Tree.id tl
      .ok (.node tl)
partial_fixpoint

def id1 {a : Type u} (t : Tree a) : Result (Tree a) :=
  match t with
  | .leaf x => .ok (.leaf x)
  | .node tl =>
    do
      let tl ← List.mapM (fun x => id1 x) tl
      .ok (.node tl)
partial_fixpoint

def id2 {a : Type u} (t : Tree a) : Result (Tree a) :=
  match t with
  | .leaf x => .ok (.leaf x)
  | .node tl =>
    do
      let tl ← List.mapM (fun x => do let _ ← id2 x; id2 x) tl
      .ok (.node tl)
partial_fixpoint

def incr (t : Tree Nat) : Result (Tree Nat) :=
  match t with
  | .leaf x => .ok (.leaf (x + 1))
  | .node tl =>
    do
      let tl ← List.mapM incr tl
      .ok (.node tl)
partial_fixpoint

def id3 (t : Tree Nat) : Result (Tree Nat) :=
  match t with
  | .leaf x => .ok (.leaf (x + 1))
  | .node tl =>
    do
      let f := id3
      let tl ← List.mapM f tl
      .ok (.node tl)
partial_fixpoint

def id4 (t : Tree Nat) : Result (Tree Nat) :=
  match t with
  | .leaf x => .ok (.leaf (x + 1))
  | .node tl =>
    do
      let f x := do
        let x1 ← id4 x
        id4 x1
      let tl ← List.mapM f tl
      .ok (.node tl)
partial_fixpoint


-- Like aeneas, we cannot handle the following

/--
error: Could not prove 'id5' to be monotone in its recursive calls:
  Cannot eliminate recursive call `id5` enclosed in
    Result.ok id5
-/
#guard_msgs in
def id5 (t : Tree Nat) : Result (Tree Nat) :=
  match t with
  | .leaf x => .ok (.leaf (x + 1))
  | .node tl =>
    do
      let f ← .ok id5
      let tl ← List.mapM f tl
      .ok (.node tl)
partial_fixpoint


end HigherOrder

structure Point where
  x : Nat
  y : Nat

def f (x : Nat) : Point :=
  let y := x + 1
  { x, y }

theorem ex1 : f x = { x, y := x + 1 } :=
  rfl

def g (p : Point) : Nat :=
  p.x + p.y

def Set (α : Type u) : Type u :=
  α → Prop

def Set.empty : Set α :=
  fun a => False

def Set.insert (s : Set α) (a : α) : Set α :=
  fun x => x = a ∨ s a

syntax (name := finSet) "{" term,* "}" : term

macro_rules (kind := finSet)
  | `({ $as,* }) => do
     as.getElems.foldlM (init := ← `(Set.empty)) fun s a => `(Set.insert $s $a)

#check { 1, 2, 3 }

#check fun x y => g {x, y}

#check fun x y : Nat => {x, y}

#check fun x y : Nat => {x, y : Point}

theorem ex2 (x y : Nat) : { x, y } = (Set.empty.insert x |>.insert y) :=
  rfl

inductive Foo where
  | foo : (String → Option Foo) → Foo

-- Would be great if this worked, but it doesn't yet:

/--
error: failed to infer structural recursion:
Cannot use parameter #2:
  failed to eliminate recursive application
    map m x
-/
#guard_msgs in
def Foo.map (m : Foo → Foo) : Foo → Foo
  | .foo f => .foo fun s => match f s with
    | none => none
    | some x => map m x
termination_by structural x => x

-- workaround:

mutual
def Foo.bar (m : Foo → Foo) : Foo → Foo
  | .foo f => .foo fun s => Foo.bar_aux m (f s)
termination_by structural x => x

def Foo.bar_aux (m : Foo → Foo) : Option Foo → Option Foo
    | none => none
    | some x => bar m x
termination_by structural x => x
end

-- similar

/--
error: failed to infer structural recursion:
Cannot use parameter xs:
  failed to eliminate recursive application
    g ys
-/
#guard_msgs in
def g (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _::ys =>
    match ys with
    | []       => 1
    | _::_::zs => g zs + 1
    | _zs       => g ys + 2
termination_by structural xs


inductive Foo2 where
  | none
  | foo : (String → Foo2) → Foo2

/--
error: failed to infer structural recursion:
Cannot use parameter #2:
  failed to eliminate recursive application
    map m (f₂ s)
-/
#guard_msgs in
def Foo2.map (m : Foo2 → Foo2) : Foo2 → Foo2
  | none => none
  | .foo f => .foo fun s => match f s with
    | none => none
    | foo f₂ => .foo fun s => map m (f₂ s)
termination_by structural x => x


/--
error: failed to infer structural recursion:
Cannot use parameter #2:
  failed to eliminate recursive application
    map_tricky m (f₂ s)
-/
#guard_msgs in
def Foo2.map_tricky (m : Foo2 → Foo2) : Foo2 → Foo2
  | none => none
  | .foo f => .foo fun s => match f s, f (s ++ s) with
    | foo f₂, foo f₃ => .foo fun s => if s = "test" then map_tricky m (f₂ s) else map_tricky m (f₃ s)
    | _, _ => none
termination_by structural x => x

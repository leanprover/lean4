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

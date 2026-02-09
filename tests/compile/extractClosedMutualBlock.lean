inductive Foo
| mk: (Int -> Foo) -> Foo
| terminal: Foo
deriving Inhabited

mutual
  partial def even (_: Unit) : Foo :=
     Foo.mk (fun i => odd () )
  partial def odd (_: Unit) : Foo :=
    Foo.mk (fun i => even ())
end

def hasLayer (f: Foo) : Bool :=
 match f with
 | Foo.mk _ => true
 | Foo.terminal => false

def main : IO Unit := do
  IO.println (if hasLayer (odd ()) then "LAYER" else "TERMINAL")
  return ()

universe u

def a : Array ((Nat × Nat) × Bool) := #[]
def b : Array Nat := #[]

structure Foo where
  (x : Array ((Nat × Nat) × Bool) := #[])
  (y : Nat := 0)

/-- info: b.modifyOp 1 fun _s => 2 : Array Nat -/
#guard_msgs in #check (b).modifyOp (idx := 1) (fun _s => 2)

/--
info: let __src := b;
__src.modifyOp 1 fun s => 2 : Array Nat
-/
#guard_msgs in #check { b with [1] := 2 }

/--
info: let __src := a;
__src.modifyOp 1 fun s =>
  (let __src := s.fst;
    (__src.fst, 1),
    s.snd) : Array ((Nat × Nat) × Bool)
-/
#guard_msgs in #check { a with [1].fst.2 := 1 }

def foo : Foo := {}

/-- info: foo.x[1]!.fst.snd : Nat -/
#guard_msgs in #check foo.x[1]!.1.2

/--
info: let __src := foo;
{
  x :=
    let __src := __src.x;
    __src.modifyOp 1 fun s => (s.fst, true),
  y := __src.y } : Foo
-/
#guard_msgs in #check { foo with x[1].2 := true }
/--
info: let __src := foo;
{
  x :=
    let __src := __src.x;
    __src.modifyOp 1 fun s =>
      (let __src := s.fst;
        (__src.fst, 1),
        s.snd),
  y := __src.y } : Foo
-/
#guard_msgs in #check { foo with x[1].fst.snd := 1 }
/--
info: let __src := foo;
{
  x :=
    let __src := __src.x;
    __src.modifyOp 1 fun s =>
      (let __src := s.fst;
        (1, __src.snd),
        s.snd),
  y := __src.y } : Foo
-/
#guard_msgs in #check { foo with x[1].1.fst := 1 }

/--
info: let __src := foo;
{
  x :=
    let __src := __src.x;
    __src.modifyOp 1 fun s =>
      (let __src := s.fst;
        (5, __src.snd),
        s.snd),
  y := __src.y } : Foo
-/
#guard_msgs in #check { foo with x[1].1.1 := 5 }
/--
info: let __src := foo;
{
  x :=
    let __src := __src.x;
    __src.modifyOp 1 fun s =>
      (let __src := s.fst;
        (__src.fst, 5),
        s.snd),
  y := __src.y } : Foo
-/
#guard_msgs in #check { foo with x[1].1.2 := 5 }

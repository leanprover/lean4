inductive T (n : Nat) where
| mk : Nat → T n
deriving Repr

instance : Inhabited (T n) where
  default := dbg_trace "evaluated default instance for n = {n}"; .mk 0

def arr : Array (T 4) := #[T.mk 1, T.mk 2, T.mk 3]

-- set_option trace.compiler.ir.result true in
def test1 : IO Unit := do
  let x := Array.get!Internal arr 1
  IO.println s!"Accessed element successfully: {repr x}"


-- set_option trace.compiler.ir.result true in
def test2 : IO Unit := do
  let x := getElem! arr 1
  -- this elaborates as expected
  -- let x := getElem! (inst := @fun _ => @instInhabitedT 4) arr 1
  IO.println s!"Accessed element successfully: {repr x}"

def test3 : IO Unit := do
  let x := arr[1]!
  IO.println s!"Accessed element successfully: {repr x}"

-- The output below should not indicate that the default instance is evaluated

/-- info: Accessed element successfully: T.mk 2 -/
#guard_msgs in #eval test1

/-- info: Accessed element successfully: T.mk 2 -/
#guard_msgs in #eval test2

/-- info: Accessed element successfully: T.mk 2 -/
#guard_msgs in #eval test3

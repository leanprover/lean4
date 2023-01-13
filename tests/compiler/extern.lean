/- Check that the extern calls do not spuriously generate `h` as an argument -/

@[extern "lean_box"]
private def box0 (sz : USize) (h : Prop) : Nat := 42

@[extern c "lean_box"]
private def box1 (sz : USize) (h : Prop) : Nat := 42

def main : IO Unit := do
  IO.println (box0 42 True)
  IO.println (box1 42 True)

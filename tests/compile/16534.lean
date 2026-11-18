/-! Regression test for mem leak in panic-ing Array.get! borrowed -/


@[noinline] def makeDefault (n : Nat) : String :=
  String.ofList (List.replicate 100000 'x') ++ toString n

@[noinline] def probe [Inhabited String] (array : @& Array String) (index : @& Nat) : Nat :=
  array[index]!.length

def loop (array : Array String) (index : Nat) : Nat → Nat → Nat
  | 0, total => total
  | n + 1, total =>
    loop array index n (total + @probe (⟨makeDefault n⟩) array index)

def main : IO UInt32 := do
  let array := #[]
  let index := 5
  IO.println s!"sum {loop array index 10 0}"
  return 0

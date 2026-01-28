initialize initNat : Nat ← pure 42

initialize ref : IO.Ref (Array String) ← IO.mkRef #[]

private initialize ref3 : Unit ← ref.modify (·.push "ref3")
initialize ref2 : Unit ← ref.modify (·.push "ref2")
initialize ref1 : Unit ← ref.modify (·.push "ref1")
private initialize ref4 : Unit ← ref.modify (·.push "ref4")

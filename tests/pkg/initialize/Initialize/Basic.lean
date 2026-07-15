module

public initialize initNat : Nat ← pure 42

public initialize ref : IO.Ref (Array String) ← IO.mkRef #[]

initialize ref3 : Unit ← ref.modify (·.push "ref3")
public initialize ref2 : Unit ← ref.modify (·.push "ref2")
public initialize ref1 : Unit ← ref.modify (·.push "ref1")
initialize ref4 : Unit ← ref.modify (·.push "ref4")

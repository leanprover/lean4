module

private def offset : Nat := 1

@[inline] public def addOffset (n : Nat) : Nat := n + offset

public def twice (n : Nat) : Nat := n + n

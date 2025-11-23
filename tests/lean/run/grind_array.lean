module
example {l : List α} {i : USize} {a : α} {h : i.toNat < l.toArray.size} :
    l.toArray.uset i a h = (l.set i.toNat a).toArray := by grind

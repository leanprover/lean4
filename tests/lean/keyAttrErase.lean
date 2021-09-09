theorem ex {i j : Fin n} (h : i = j) : i.val = j.val :=
  h ▸ rfl

attribute [-appUnexpander] unexpandEqNDRec

#print ex

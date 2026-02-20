abbrev shrinkFn (α : Type u) [sz : SizeOf α] := (x : α) → List { y : α // sz.sizeOf y < sz.sizeOf x }

class Sampleable (α : Type u) [SizeOf α] where
  shrink : shrinkFn α := fun _ => []

def Prod.shrink [SizeOf α] [SizeOf β] (shrA : shrinkFn α) (shrB : shrinkFn β) : shrinkFn (α × β) := fun (fst, snd) =>
  let shrink1 := shrA fst |>.map fun ⟨x, _⟩ => ⟨(x, snd), by simp_all +arith⟩
  let shrink2 := shrB snd |>.map fun ⟨x, _⟩ => ⟨(fst, x), by simp_all +arith⟩
  shrink1 ++ shrink2

universe variable u
variable {α : Type u}

def split : list α → list α × list α
| []            := ([], [])
| [a]           := ([a], [])
| (a :: b :: l) := (a :: (split l).1, b :: (split l).2)


universe u
variable {α : Type u}

def split : List α → List α × List α
| []       => ([], [])
| [a]      => ([a], [])
| a::b::as => (a :: (split as).1, b :: (split as).2)

theorem ex1 : split [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) :=
rfl

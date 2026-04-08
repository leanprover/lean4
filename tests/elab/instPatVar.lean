class Pretty (α : Type u) where
  pretty : α → Std.Format

export Pretty (pretty)

def concat (xs : List ((α : Type u) × Pretty α × α)) : Std.Format :=
  match xs with
  | [] => ""
  | ⟨_, _, v⟩ :: xs => pretty v ++ concat xs

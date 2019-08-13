inductive Term : Type
| app : List Term -> Term

namespace Term

instance : Inhabited Term := ⟨app []⟩

partial def transform (f : Term -> Option Term) : Term -> Term
| t =>
  match f t with
  | some u => transform u
  | none   =>
    match t with
    | app args =>
      let newArgs := args.map (fun arg => transform arg);
      transform (app newArgs)

end Term

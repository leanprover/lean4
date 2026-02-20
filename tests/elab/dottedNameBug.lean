inductive AltCore (α : Type)
  | default (val : α)
  | alt (name : String) (val : α)

inductive Code where
  | cases (alt: AltCore Code)
  | return (id : Nat)

abbrev Alt := AltCore Code

def AltCore.getCode : Alt → Code
  | .default c => c
  | .alt _ c => c

def AltCore.update (alt : Alt) (c : Code) : Alt :=
  match alt with
  | .default _ => if true then alt else .default c
  | .alt n _ => if true then alt else .alt n c

example (alt : Alt) : Code :=
  alt.getCode

def Alt.getCode' : Alt → Code
  | .default c => c
  | .alt _ c => c

example (alt : Alt) : Code :=
  if true then .return 1 else alt.getCode'

example (alt : Alt) : Code :=
  if true then alt.getCode' else .return 0

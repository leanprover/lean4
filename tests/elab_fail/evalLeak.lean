import Lean

#eval match true with | true => false | false => true

open Lean Elab Command Meta
#eval show CommandElabM Unit from do
  match ([] : List Nat) with
  | []  =>
    liftCoreM <| addDecl <| Declaration.defnDecl {
      name        := `foo
      type        := Lean.mkConst ``Bool
      levelParams := []
      value       := Lean.mkConst ``true
      hints       := .opaque
      safety      := .safe
    }
  | _ => return ()

#check foo
-- The auxiliary declarations created to elaborate the commands above
-- should not leak into the environment
#check _eval.match_1 -- Should fail
#check _eval.match_2 -- Should fail

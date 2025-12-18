import Lean
open Lean.SubExpr

def ps := [#[], #[0], #[1], #[0,1], #[1,0] , #[0,0], #[1,2,3]]
theorem Pos.roundtrip :
  true = ps.all fun x => x == (Pos.toArray <| Pos.ofArray <| x)
  := by native_decide

theorem Pos.append_roundtrip :
  true = (List.all
    (ps.flatMap fun p => ps.map fun q => (p,q))
    (fun (x,y) => (x ++ y) == (Pos.toArray <| (Pos.append (Pos.ofArray x) (Pos.ofArray y))))
  ) := by native_decide

theorem Pos.stringRoundtrip :
  true = ps.all (fun p =>
    let x := Pos.ofArray p
    some x == (Except.toOption $ Pos.fromString? $ Pos.toString $ x)
  ) := by native_decide

#guard Pos.toString Nat.zero == "/"

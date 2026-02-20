import Lean
open Lean

@[noinline] def noinline (a : α) := a

#eval
  let b := levelZero
  let a1 := mkLevelParam `a
  let a2 := mkLevelParam (noinline `a)
  let l := mkLevelMax a1 b
  (l.updateMax! a1 b).isMax == (l.updateMax! a2 b).isMax

#eval
  let b := levelZero
  let a1 := mkLevelParam `a
  let l := mkLevelMax a1 b
  assert! (l.updateMax! a1 b) == a1
  toString (l.updateMax! a1 b)

#eval
  let b := mkLevelParam `b
  let a1 := mkLevelParam `a
  let l := mkLevelMax a1 b
  assert! (l.updateMax! a1 b) == l
  assert! ptrAddrUnsafe (l.updateMax! a1 b) == ptrAddrUnsafe l
  toString (l.updateMax! a1 b)

import Std
import Lean

open Lean Compiler LCNF

/-!
`@[csimp]` should only be applied to `noncomputable` defs so we never compile against the wrong
version. The following list shows where this is not yet the case.
-/

/--
info: (Acc.rec, Acc.recC)
(Array.instDecidableEmpEq, Array.instDecidableEmpEqImpl)
(Array.instDecidableEq, Array.instDecidableEqImpl)
(Array.instDecidableEqEmp, Array.instDecidableEqEmpImpl)
(Array.pmap, Array.pmapImpl)
(ByteArray.append, ByteArray.fastAppend)
(List.append, List.appendTR)
(List.dropLast, List.dropLastTR)
(List.erase, List.eraseTR)
(List.eraseP, List.erasePTR)
(List.filter, List.filterTR)
(List.findRev?, List.findRev?TR)
(List.flatMap, List.flatMapTR)
(List.flatten, List.flattenTR)
(List.foldr, List.foldrTR)
(List.insertIdx, List.insertIdxTR)
(List.intercalate, List.intercalateTR)
(List.intersperse, List.intersperseTR)
(List.leftpad, List.leftpadTR)
(List.length, List.lengthTR)
(List.map, List.mapTR)
(List.merge, List.MergeSort.Internal.mergeTR)
(List.mergeSort, List.MergeSort.Internal.mergeSortTR₂)
(List.modify, List.modifyTR)
(List.pmap, List.pmapImpl)
(List.range', List.range'TR)
(List.replace, List.replaceTR)
(List.replicate, List.replicateTR)
(List.set, List.setTR)
(List.take, List.takeTR)
(List.takeWhile, List.takeWhileTR)
(List.unzip, List.unzipTR)
(List.zipIdx, List.zipIdxTR)
(List.zipWith, List.zipWithTR)
(Nat.all, Nat.allTR)
(Nat.any, Nat.anyTR)
(Nat.fold, Nat.foldTR)
(Nat.rec, Nat.recCompiled)
(Nat.repeat, Nat.repeatTR)
(String.utf8EncodeChar, String.utf8EncodeCharFast)
(Thunk.fn, Thunk.fnImpl)
(Vector.pmap, Vector.pmapImpl)
(String.Slice.Pos.next, String.Slice.Pos.nextFast)
-/
#guard_msgs in
run_elab do
  let env ← getEnv
  for (l, r) in CSimp.ext.getState env |>.map.toList.mergeSort (le := (·.1.lt ·.1)) do
    if !isNoncomputable env l then
      IO.println (l, r)

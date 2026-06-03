import Std.Sat.AIG

open Std.Sat AIG

def mkTwoAtoms : (aig : AIG Nat) × BinaryInput aig :=
  let aig : AIG Nat := .empty

  let res := aig.mkAtom 0
  let aig := res.aig
  let lhs := res.ref

  let res := aig.mkAtom 1
  let aig := res.aig
  let rhs := res.ref
  let lhs := lhs.cast <| LawfulOperator.le_size (f := mkAtom) ..

  ⟨aig, ⟨lhs, rhs⟩⟩

def mkXor : Entrypoint Nat :=
  let ⟨aig, inputs⟩ := mkTwoAtoms
  aig.mkXorCached inputs

-- Check mkXorCached and its inversion are detected as XORs

/-- info: true -/
#guard_msgs in
#eval AIG.detectXor mkXor |>.isSome

/-- info: true -/
#guard_msgs in
#eval AIG.detectXor ⟨mkXor.aig, mkXor.ref.flip true⟩ |>.isSome

-- Check that the CNF lowering uses a 4-clause encoding for XOR
/--
info: { clauses := #[[(1, true), (6, false)], [(1, false), (6, true)], [(2, true), (7, false)], [(2, false), (7, true)],
               [(5, false), (1, false), (2, false)], [(5, false), (1, true), (2, true)],
               [(5, true), (1, false), (2, true)], [(5, true), (1, true), (2, false)], [(5, true)]] }
-/
#guard_msgs in
#eval AIG.toCNF mkXor

def mkXorAnds (inv invl invr : Bool) (perm : Bool) : Entrypoint Nat :=
  let ⟨aig, ⟨lhs, rhs⟩⟩ := mkTwoAtoms
  let lhs := lhs.flip invl
  let rhs := rhs.flip invr

  let res := aig.mkGate ⟨lhs,  rhs⟩
  let aig := res.aig
  let l := res.ref

  let lhsinv := lhs.flip true |>.cast <| LawfulOperator.le_size (f := mkGate) ..
  let rhsinv := rhs.flip true |>.cast <| LawfulOperator.le_size (f := mkGate) ..

  let res := aig.mkGate (if perm then ⟨rhsinv,  lhsinv⟩ else ⟨lhsinv, rhsinv⟩)
  let aig := res.aig
  let r := res.ref
  let l := l.cast <| LawfulOperator.le_size (f := mkGate) ..

  let res := aig.mkGate ⟨l.flip true, r.flip true⟩
  let aig := res.aig
  let root := res.ref.flip inv

  ⟨aig, root⟩

-- Check that all NPN variations of the two-level XOR are detected as XORs
/-- info: true -/
#guard_msgs in
#eval ∀ inv invl invr perm, AIG.detectXor (mkXorAnds inv invl invr perm) |>.isSome

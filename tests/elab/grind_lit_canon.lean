/-!
Tests that the canonicalizer (`Sym.Canon.normNumLit?`) maps all spellings of the same
numeric literal of a wrapping type (`BitVec`, `Fin`, `UInt8`/…/`UInt64`) to a single
representation before they reach the E-graph: `BitVec.ofNat`/`BitVec.ofNatLT`/`Fin.ofNat`
spellings are converted to `OfNat.ofNat`, and out-of-range numerals are reduced modulo the
type's cardinality. Two representations of the same value used to reach the E-graph as
distinct interpreted nodes, and `grind` produced an invalid inconsistency proof rejected
by the kernel. `grind.debug` enables the E-graph invariant check that all interpreted
nodes are in canonical form.
-/

set_option linter.unusedVariables false
set_option grind.debug true

/-! `Fin.ofNat` vs `OfNat.ofNat` -/

example (x : Fin 3) (h1 : x = Fin.ofNat 3 2) (h2 : x = (2 : Fin 3)) : True := by grind
example (x : Fin 3) (h1 : x = Fin.ofNat 3 2) : x = (2 : Fin 3) := by grind
example (x : Fin 3) (h1 : x = Fin.ofNat 3 5) : x = (2 : Fin 3) := by grind
example (x : Fin 3) (h1 : x = Fin.ofNat 3 2) (h2 : x = (1 : Fin 3)) : False := by grind

/-! Out-of-range `Fin` literals -/

example (x : Fin 3) (h1 : x = (5 : Fin 3)) : x = (2 : Fin 3) := by grind
example (x : Fin 3) (h1 : x = (5 : Fin 3)) (h2 : x = (1 : Fin 3)) : False := by grind

/-! Out-of-range `UInt8`/…/`UInt64` literals -/

example (x : UInt8) (h1 : x = (300 : UInt8)) (h2 : x = (44 : UInt8)) : True := by grind
example (x : UInt8) (h1 : x = (300 : UInt8)) : x = (44 : UInt8) := by grind
example (x : UInt8) (h1 : x = (300 : UInt8)) (h2 : x = (45 : UInt8)) : False := by grind
example (x : UInt16) (h1 : x = (70000 : UInt16)) : x = (4464 : UInt16) := by grind
example (x : UInt32) (h1 : x = (4294967296 : UInt32)) : x = (0 : UInt32) := by grind
example (x : UInt64) (h1 : x = (18446744073709551616 : UInt64)) : x = (0 : UInt64) := by grind
example (x : Int8) (h1 : x = (300 : Int8)) : x = (44 : Int8) := by grind
example (x : Int16) (h1 : x = (70000 : Int16)) : x = (4464 : Int16) := by grind

/-! Out-of-range `BitVec` `OfNat` literal hidden in a `dite` `Decidable` instance -/

example (x : BitVec 4) (h1 : x = (17 : BitVec 4)) :
    (if x = (1 : BitVec 4) then 0 else 1) = 0 := by grind

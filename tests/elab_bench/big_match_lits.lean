import Lean

/-!
Generates the equation lemmas of definitions by `match` on many literals of type `Nat`, `Int`,
`Char`, `UInt8`, `Fin n`, and `BitVec n`, each with a catch-all case.
See `big_match_string.lean` for `String` literals.
-/

set_option Elab.async false

open Lean Elab Command

/--
Defines `f : type → Nat` by `match` on the `n` literals `mkLit 0`, ..., `mkLit (n-1)` and a
catch-all case, and generates its equation lemmas.
-/
def testGen (f : Name) (type : Term) (n : Nat) (mkLit : Nat → CommandElabM Term) :
    CommandElabM Unit := do
  let f := mkIdent f
  let cases ← (Array.range n).mapM fun i => do
    `(Lean.Parser.Term.matchAltExpr| | $(← mkLit i) => $(Syntax.mkNatLit i))
  let cases := cases.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $(Syntax.mkNatLit n)))
  elabCommand (← `(def $f:ident : $type → Nat $cases:matchAlt*))
  let some eqns ← liftTermElabM <| Meta.getEqnsFor? f.getId
    | throwError "no equation lemmas for `{f}`"
  unless eqns.size == n + 1 do
    throwError "expected {n + 1} equation lemmas, got {eqns.size}"

#eval show CommandElabM Unit from do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 128 else 32
  let num (i : Nat) : CommandElabM Term := pure (Syntax.mkNatLit i)
  -- The literals are not consecutive numbers.
  testGen `natLits (← `(Nat)) n fun i => num (3 * i + 1)
  testGen `intLits (← `(Int)) n fun i => do
    if i % 2 == 0 then num (3 * i) else `(-$(Syntax.mkNatLit (3 * i)))
  testGen `charLits (← `(Char)) n fun i => pure (Syntax.mkCharLit (Char.ofNat (3 * i + 256)))
  testGen `uint8Lits (← `(UInt8)) n fun i => num (i + 7)
  testGen `finLits (← `(Fin 1024)) n fun i => num (3 * i + 1)
  testGen `bitVecLits (← `(BitVec 16)) n fun i => `(BitVec.ofNat 16 $(Syntax.mkNatLit (3 * i + 1)))

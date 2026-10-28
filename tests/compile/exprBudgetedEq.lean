module
import Lean

/-!
Tests budgeted expression equality for #15985: exact answers, exhaustion, binder modes,
sharing-dependent results, leaf fast paths, application spines, shared DAGs, and budget protection
for string literals and metadata.
-/

open Lean

private def expect (label : String) (actual expected : LBool) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {expected}, got {actual}"

private def expectBoth (label : String) (a b : Expr) (budget : USize)
    (expected : LBool) : IO Unit := do
  expect (label ++ " (eqv)") (← a.eqvBudgeted b budget) expected
  expect (label ++ " (equal)") (← a.equalBudgeted b budget) expected

private unsafe def expectDistinct (a b : Expr) : IO Unit := do
  if ptrEq a b then
    throw <| IO.userError "test requires separately allocated expressions"

@[noinline] private def chain (n : Nat) (left : Bool := false) (dag : Bool := false) : IO Expr := do
  let r ← IO.mkRef (mkConst `z)
  for _ in [:n] do
    r.modify fun e =>
      if dag then mkApp e e
      else if left then mkApp e (mkConst `a)
      else mkApp (mkConst `f) e
  r.get

@[noinline] private def longName (n : Nat) : IO Name := do
  let r ← IO.mkRef Name.anonymous
  for _ in [:n] do
    r.modify fun n => .str n "part"
  r.get

@[noinline] private def longLevel (n : Nat) : IO Level := do
  let r ← IO.mkRef Level.zero
  for _ in [:n] do
    r.modify Level.succ
  r.get

@[noinline] private def longString (n : Nat) (c : Char := 'x') : IO String := do
  let r ← IO.mkRef ""
  for _ in [:n] do
    r.modify (·.push c)
  r.get

@[noinline] private def stringExpr (s : String) : IO Expr := do
  let r ← IO.mkRef s
  return mkStrLit (← r.get)

@[noinline] private def bigNat (n : Nat) : IO Nat := do
  let r ← IO.mkRef 1
  for _ in [:n] do
    r.modify (· * 256)
  r.get

@[noinline] private def metadata (n : Nat) : IO MData := do
  let r ← IO.mkRef ([] : List (Name × DataValue))
  for i in [:n] do
    r.modify fun es => (.num `key i, .ofNat i) :: es
  return { entries := ← r.get }

@[noinline] private def metadataExpr (entries : List (Name × DataValue)) : IO Expr := do
  let r ← IO.mkRef entries
  return mkMData { entries := ← r.get } (mkBVar 0)

@[noinline] private def metadataCons (key : Name) (value : DataValue)
    (tail : List (Name × DataValue) := []) : IO Expr := do
  let r ← IO.mkRef tail
  metadataExpr ((key, value) :: (← r.get))

@[noinline] private def metadataString (s : String) : IO Expr := do
  let r ← IO.mkRef s
  metadataCons `key (.ofString (← r.get))

@[noinline] private def syntaxDag (n : Nat) : IO Expr := do
  let r ← IO.mkRef (Syntax.atom .none "leaf")
  for _ in [:n] do
    r.modify fun s => Syntax.node .none `pair #[s, s]
  return mkMData { entries := [(`key, .ofSyntax (← r.get))] } (mkConst `Nat)

private unsafe def checkCopies (label : String) (mk : IO Expr) : IO Unit := do
  let a ← mk
  let b ← mk
  expectDistinct a b
  expectBoth (label ++ " exhausted") a b 16 .undef
  expectBoth (label ++ " sufficient") a b 100000 .true
  expectBoth (label ++ " pointer") a a 0 .true

private unsafe def checkUnchargedPayload (label : String) (mk : IO Expr) : IO Unit := do
  let a ← mk
  let b ← mk
  expectDistinct a b
  expectBoth (label ++ " expression budget") a b 0 .undef
  expectBoth (label ++ " payload uncharged") a b 1 .true

private unsafe def checkLeafCopies (label : String) (mk : IO Expr) : IO Unit := do
  let a ← mk
  let b ← mk
  expectDistinct a b
  expectBoth (label ++ " leaf fast path") a b 0 .true

private unsafe def checkStringBudget (c : Char) (bytes : USize) : IO Unit := do
  let s₁ ← longString 32 c
  let s₂ ← longString 32 c
  let a ← stringExpr s₁
  let b ← stringExpr s₂
  expectDistinct a b
  expectBoth "string below budget" a b (bytes - 1) .undef
  expectBoth "string exact budget" a b bytes .true
  let shared ← stringExpr s₁
  expectDistinct a shared
  expectBoth "shared string payload" a shared 0 .true

private unsafe def checkMetadataStringBudget (c : Char) (bytes : USize) : IO Unit := do
  let s₁ ← longString 32 c
  let s₂ ← longString 32 c
  let a ← metadataString s₁
  let b ← metadataString s₂
  expectDistinct a b
  expectBoth "metadata string below budget" a b (bytes + 1) .undef
  expectBoth "metadata string exact budget" a b (bytes + 2) .true
  let shared ← metadataString s₁
  expectDistinct a shared
  match a, shared with
  | .mdata md₁ _, .mdata md₂ _ =>
    if ptrEq md₁.entries.head!.2 md₂.entries.head!.2 then
      throw <| IO.userError "test requires separate DataValue wrappers"
  | _, _ => throw <| IO.userError "expected metadata"
  expectBoth "shared metadata string payload" a shared 2 .true
  let differentLength ← metadataString (← longString 33 c)
  expectBoth "metadata string length mismatch" a differentLength 2 .false

private unsafe def checkUnchargedMetadata (label : String)
    (mk : IO (Name × DataValue)) : IO Unit := do
  let (k₁, v₁) ← mk
  let (k₂, v₂) ← mk
  let a ← metadataCons k₁ v₁
  let b ← metadataCons k₂ v₂
  expectDistinct a b
  expectBoth (label ++ " entry budget") a b 1 .undef
  expectBoth (label ++ " payload uncharged") a b 2 .true

private unsafe def checkMetadata : IO Unit := do
  let empty₁ ← metadataExpr []
  let empty₂ ← metadataExpr []
  expectDistinct empty₁ empty₂
  expectBoth "empty metadata" empty₁ empty₂ 1 .true
  for n in [1, 8, 128] do
    let a ← metadataExpr (← metadata n).entries
    let b ← metadataExpr (← metadata n).entries
    expectDistinct a b
    expectBoth "metadata entries below budget" a b n.toUSize .undef
    expectBoth "metadata entries exact budget" a b (n + 1).toUSize .true
  let tail := (← metadata 128).entries
  let a ← metadataExpr tail
  let b ← metadataExpr tail
  expectDistinct a b
  expectBoth "shared metadata map" a b 1 .true
  let a ← metadataCons `first (.ofNat 0) tail
  let b ← metadataCons `first (.ofNat 0) tail
  expectDistinct a b
  expectBoth "shared metadata tail" a b 2 .true
  let sharedValue := DataValue.ofSyntax (.atom .none (← longString 4096))
  let a ← metadataCons `key sharedValue
  let b ← metadataCons `key sharedValue
  expectDistinct a b
  expectBoth "shared metadata value" a b 2 .true
  let long₁ := (← metadata 128).entries
  let long₂ := (← metadata 128).entries
  let a ← metadataCons `first (.ofNat 0) long₁
  let b ← metadataCons `different (.ofNat 0) long₂
  expectBoth "metadata key mismatch before tail" a b 2 .false
  let b ← metadataCons `first (.ofNat 1) long₂
  expectBoth "metadata value mismatch before tail" a b 2 .false
  let b ← metadataCons `first (.ofString (← longString 4096)) long₂
  expectBoth "metadata kind mismatch before tail" a b 2 .false
  let short ← metadataCons `first (.ofNat 0)
  expectBoth "metadata length mismatch" a short 2 .false
  expectBoth "metadata length mismatch symmetric" short a 2 .false
  let a ← metadataExpr [(`a, .ofNat 0), (`b, .ofNat 1)]
  let b ← metadataExpr [(`b, .ofNat 1), (`a, .ofNat 0)]
  expectBoth "metadata entry order matters" a b 2 .false
  let values := [DataValue.ofString "a", .ofString "b", .ofBool false, .ofBool true,
    .ofName `a, .ofName `b, .ofNat 0, .ofNat 1, .ofInt (-1), .ofInt 1,
    .ofSyntax (.atom .none "a"), .ofSyntax (.atom .none "b"),
    .ofSyntax (.atom (.synthetic ⟨0⟩ ⟨1⟩) "a")]
  for v₁ in values do
    for v₂ in values do
      let a ← metadataCons `key v₁
      let b ← metadataCons `key v₂
      expectBoth "metadata agrees with exact equality" a b 100000 (a == b).toLBool

private def checkModes : IO Unit := do
  let ty := mkConst `Nat
  let body := mkBVar 0
  for ctor in [Expr.lam, Expr.forallE] do
    let a := ctor `x ty body .default
    let renamed := ctor `y ty body .default
    let implicit := ctor `x ty body .implicit
    for b in [renamed, implicit] do
      unless a.hash == b.hash do
        throw <| IO.userError "expected binder-only differences to have the same hash"
      expect "binder eqv" (← a.eqvBudgeted b 100) .true
      expect "binder equal" (← a.equalBudgeted b 100) .false
  let a := Expr.letE `x ty (mkNatLit 1) body false
  let b := Expr.letE `y ty (mkNatLit 1) body false
  expect "let name eqv" (← a.eqvBudgeted b 100) .true
  expect "let name equal" (← a.equalBudgeted b 100) .false

private def checkCorpus : IO Unit := do
  let nat := mkConst `Nat
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let md₁ : MData := { entries := [(`key, .ofNat 1)] }
  let md₂ : MData := { entries := [(`key, .ofNat 2)] }
  let stx₁ := Syntax.atom .none "token"
  let stx₂ := Syntax.atom (.synthetic ⟨0⟩ ⟨5⟩) "token"
  let mut es := #[mkBVar 0, mkBVar 1, mkFVar ⟨`x⟩, mkFVar ⟨`y⟩,
    mkMVar ⟨`x⟩, mkMVar ⟨`y⟩, mkSort .zero, mkSort (.succ .zero),
    nat, mkConst `f [.param `u], mkConst `f [.mvar ⟨`u⟩],
    mkConst `f [.max (.param `u) (.succ .zero)],
    mkConst `f [.imax (.param `u) (.succ .zero)],
    zero, one, mkRawNatLit 0, mkRawNatLit 1, mkStrLit "a", mkStrLit "b", mkApp nat zero,
    Expr.lam `x nat (mkBVar 0) .default, Expr.lam `y nat (mkBVar 0) .implicit,
    Expr.forallE `x nat nat .default, Expr.forallE `y nat nat .implicit,
    Expr.letE `x nat zero (mkBVar 0) false, Expr.letE `y nat zero (mkBVar 0) true,
    mkMData md₁ zero, mkMData md₂ zero, Expr.proj `S 0 zero, Expr.proj `S 1 zero,
    mkMData { entries := [(`key, .ofSyntax stx₁)] } zero,
    mkMData { entries := [(`key, .ofSyntax stx₂)] } zero]
  for i in [:32] do
    es := es.push (mkApp es[i]! es[(i + 1) % es.size]!)
  for a in es do
    for b in es do
      for budget in ([0, 1, 4, 16, 100000] : List USize) do
        let eqv ← a.eqvBudgeted b budget
        let equal ← a.equalBudgeted b budget
        unless eqv == .undef || eqv == (a == b).toLBool do
          throw <| IO.userError "budgeted eqv disagrees with eqv"
        unless equal == .undef || equal == (Expr.equal a b).toLBool do
          throw <| IO.userError "budgeted equal disagrees with equal"
        expect "symmetric eqv" eqv (← b.eqvBudgeted a budget)
        expect "symmetric equal" equal (← b.equalBudgeted a budget)
        if budget == 100000 then
          expect "complete eqv" eqv (a == b).toLBool
          expect "complete equal" equal (Expr.equal a b).toLBool

public unsafe def main : IO Unit := do
  expectBoth "hash mismatch with no budget" (mkNatLit 0) (mkNatLit 1) 0 .false
  let a ← chain 1
  let b ← chain 1
  expectDistinct a b
  expectBoth "no budget" a b 0 .undef
  expectBoth "one application" a b 1 .true
  expectBoth "shared, no budget" a a 0 .true
  checkModes
  checkCorpus
  checkMetadata
  checkCopies "argument chain" (chain 1024)
  checkCopies "function spine" (chain 10000 true)
  let a ← chain 8 true
  let b ← chain 8 true
  expectDistinct a b
  expectBoth "function spine below budget" a b 7 .undef
  expectBoth "function spine exact budget" a b 8 .true
  let a ← chain 40 false true
  let b ← chain 40 false true
  expectDistinct a b
  expectBoth "shared DAG exhausted" a b 40 .undef
  expectBoth "shared DAG sufficient" a b 100000 .true
  checkLeafCopies "bound variable" (do
    let r ← IO.mkRef 0
    return mkBVar (← r.get))
  checkLeafCopies "free variable" (return mkFVar ⟨← longName 1024⟩)
  checkLeafCopies "metavariable" (return mkMVar ⟨← longName 1024⟩)
  checkLeafCopies "level" (return mkSort (← longLevel 1024))
  checkLeafCopies "small natural literal" (do
    let r ← IO.mkRef 42
    return mkRawNatLit (← r.get))
  checkLeafCopies "large natural literal" (return mkRawNatLit (← bigNat 1024))
  checkStringBudget 'x' 32
  checkStringBudget 'α' 64
  checkUnchargedPayload "name" (return mkConst (← longName 1024))
  checkUnchargedPayload "name string" (return mkConst (.str .anonymous (← longString 4096)))
  checkUnchargedPayload "level list" (do
    let r ← IO.mkRef ([] : List Level)
    for _ in [:1024] do
      r.modify (.zero :: ·)
    return mkConst `f (← r.get))
  checkCopies "string literal" (return mkStrLit (← longString 4096))
  checkCopies "metadata" (return mkMData (← metadata 128) (mkConst `Nat))
  checkUnchargedMetadata "metadata key" (return (← longName 1024, .ofNat 0))
  checkUnchargedMetadata "metadata name" (return (`key, .ofName (← longName 1024)))
  checkUnchargedMetadata "metadata natural" (return (`key, .ofNat (← bigNat 1024)))
  checkUnchargedMetadata "metadata integer" (return (`key, .ofInt (-Int.ofNat (← bigNat 1024))))
  checkMetadataStringBudget 'x' 32
  checkMetadataStringBudget 'α' 64
  checkCopies "metadata string" (do
    let md : MData := { entries := [(`key, .ofString (← longString 4096))] }
    return mkMData md (mkConst `Nat))
  checkCopies "metadata syntax" (do
    let stx := Syntax.atom .none (← longString 4096)
    return mkMData { entries := [(`key, .ofSyntax stx)] } (mkConst `Nat))
  checkCopies "metadata syntax array" (do
    let r ← IO.mkRef (#[] : Array Syntax)
    for _ in [:1024] do
      r.modify (·.push .missing)
    let stx := Syntax.node .none `node (← r.get)
    return mkMData { entries := [(`key, .ofSyntax stx)] } (mkConst `Nat))
  let a ← syntaxDag 40
  let b ← syntaxDag 40
  expectDistinct a b
  expectBoth "syntax DAG exhausts" a b 100 .undef

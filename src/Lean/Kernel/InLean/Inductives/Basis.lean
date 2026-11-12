/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.BlockShape
public import Lean.Kernel.InLean.Pins

/-!
# InLean's inductive check: the pinned basis blocks and `And`

Twin of `ConLeche.Kernel.Basis` (with the pins of `ConLeche.Kernel.Basis.Eq`,
`.Nat`, `.Empty`, `.False` and `.And`).  A pinned block is generated and
checked like any other block; the reserved names' check after it
(`Lean.Kernel.InLean.basisNamesOk`) compares it with the pin, up to its level parameters'
names.  The pins are Lean entries, and a block is compared with one by
`pinCopyOk`: names, level-parameter count, type and rules up to `mdata` and
binder names and infos (con-leche's terms carry neither), and what
con-leche's records carry besides (a constructor's counts; a recursor's
major index, rule prefix, K flag and rules' constructors and field counts).
An inductive's other fields are the block's (`Lean.Kernel.InLean.genEntriesAgree`
checks them against its shape), as con-leche's capabilities are its
install's.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean BasisDSL

/-- A pinned inductive type former. -/
def indPin (n : Name) (lps : List Name) (ty : Expr) (nP nIdx : Nat) (ctors : List Name)
    (isRec : Bool := false) : ConstantInfo :=
  .inductInfo { name := n, levelParams := lps, type := ty, numParams := nP, numIndices := nIdx,
                all := [n], ctors, numNested := 0, isRec, isUnsafe := false,
                isReflexive := false }

/-- A pinned constructor. -/
def ctorPin (n : Name) (lps : List Name) (ty : Expr) (T : Name) (cidx nP nF : Nat) :
    ConstantInfo :=
  .ctorInfo { name := n, levelParams := lps, type := ty, induct := T, cidx, numParams := nP,
              numFields := nF, isUnsafe := false }

/-- A pinned recursor at `(mI, rP)` (the encoding of `recEntry`). -/
def recPin (n : Name) (lps : List Name) (ty : Expr) (T : Name) (mI rP : Nat) (isK : Bool)
    (rules : List RecursorRule) : ConstantInfo :=
  .recInfo { name := n, levelParams := lps, type := ty, all := [T], numParams := rP,
             numIndices := mI - rP, numMotives := 0, numMinors := 0, rules, k := isK,
             isUnsafe := false }

/-- Twin of `rule` (`ConLeche.Kernel.Basis.Builder`). -/
def rule (ctor : Name) (nfields : Nat) (rhs : Expr) : RecursorRule := ⟨ctor, nfields, rhs⟩

/-! ## The pins -/

/-- Twin of `eqRecMotive`. -/
def eqRecMotive : Expr :=
  pi "b" (bv 1) <|
  pi "t" (ap3 (cnst eqName [u]) (bv 2) (bv 1) (bv 0)) (srt u1)

/-- Twin of `eqBasis`. -/
def eqBasis : List ConstantInfo :=
  [indPin eqName [uN]
    (piI "α" (srt u) <|
     pi "a" (bv 0) <|
     pi "b" (bv 1) prop)
    2 1 [eqReflName],
   ctorPin eqReflName [uN]
    (piI "α" (srt u) <|
     pi "a" (bv 0) <|
     ap3 (cnst eqName [u]) (bv 1) (bv 0) (bv 0))
    eqName 0 2 0,
   recPin (eqName.str "rec") [u1N, uN]
    (piI "α" (srt u) <|
     piI "a" (bv 0) <|
     piI "motive" eqRecMotive <|
     pi "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <|
     piI "b" (bv 3) <|
     pi "t" (ap3 (cnst eqName [u]) (bv 4) (bv 3) (bv 0)) <|
     ap2 (bv 3) (bv 1) (bv 0))
    eqName 5 4 true
    [rule eqReflName 0 <|
      lmI "α" (srt u) <|
      lm "a" (bv 0) <|
      lm "motive" eqRecMotive <|
      lm "refl" (ap2 (bv 0) (bv 1) (ap2 (cnst eqReflName [u]) (bv 2) (bv 1))) <|
      bv 0]]

/-- Twin of `natT`. -/
def natT : Expr := cnst natName

/-- Twin of `natRecMotive`. -/
def natRecMotive : Expr := pi "t" natT (srt u)

/-- Twin of `natRecSucc`. -/
def natRecSucc : Expr :=
  pi "n" natT <|
  pi "n_ih" (.app (bv 2) (bv 0)) <|
  .app (bv 3) (.app (cnst natSuccName) (bv 1))

/-- Twin of `natBasis`. -/
def natBasis : List ConstantInfo :=
  [indPin natName [] type1 0 0 [natZeroName, natSuccName] (isRec := true),
   ctorPin natZeroName [] natT natName 0 0 0,
   ctorPin natSuccName [] (pi "n" natT natT) natName 1 0 1,
   recPin (natName.str "rec") [uN]
    (piI "motive" natRecMotive <|
     pi "zero" (.app (bv 0) (cnst natZeroName)) <|
     pi "succ" natRecSucc <|
     pi "t" natT (.app (bv 3) (bv 0)))
    natName 3 3 false
    [rule natZeroName 0 <|
      lm "motive" natRecMotive <|
      lm "zero" (.app (bv 0) (cnst natZeroName)) <|
      lm "succ" natRecSucc <|
      bv 1,
     rule natSuccName 1 <|
      lm "motive" natRecMotive <|
      lm "zero" (.app (bv 0) (cnst natZeroName)) <|
      lm "succ" natRecSucc <|
      lm "n" natT <|
      ap2 (bv 1) (bv 0) (ap4 (cnst (natName.str "rec") [u]) (bv 3) (bv 2) (bv 1) (bv 0))]]

/-- Twin of `emptyBasis`. -/
def emptyBasis : List ConstantInfo :=
  [indPin `Empty [] type1 0 0 [],
   recPin `Empty.rec [uN]
    (pi "motive" (pi "t" (cnst `Empty) (srt u)) <|
     pi "t" (cnst `Empty) (.app (bv 1) (bv 0)))
    `Empty 1 1 false []]

/-- Twin of `falseBasis`. -/
def falseBasis : List ConstantInfo :=
  [indPin `False [] prop 0 0 [],
   recPin `False.rec [uN]
    (pi "motive" (pi "t" (cnst `False) (srt u)) <|
     pi "t" (cnst `False) (.app (bv 1) (bv 0)))
    `False 1 1 false []]

/-- Twin of `andRecName`. -/
def andRecName : Name := andName.str "rec"

/-- Twin of `andRecMotive`. -/
def andRecMotive : Expr :=
  pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)

/-- Twin of `andRecMinor`. -/
def andRecMinor : Expr :=
  pi "left" (bv 2) <|
  pi "right" (bv 2) <|
  .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))

/-- Twin of `andPin`; as a structure, `And` is not recursive and its former's
entry is the one a generated block has. -/
def andPin : List ConstantInfo :=
  [indPin andName [] (pi "a" prop (pi "b" prop prop)) 2 0 [andIntroName],
   ctorPin andIntroName []
    (piI "a" prop <|
     piI "b" prop <|
     pi "left" (bv 1) <|
     pi "right" (bv 1) <|
     ap2 (cnst andName) (bv 3) (bv 2))
    andName 0 2 2,
   recPin andRecName [uN]
    (piI "a" prop <|
     piI "b" prop <|
     piI "motive" andRecMotive <|
     pi "intro" andRecMinor <|
     pi "t" (ap2 (cnst andName) (bv 3) (bv 2)) <|
     .app (bv 2) (bv 0))
    andName 4 4 false
    [rule andIntroName 2 <|
      lmI "a" prop <|
      lmI "b" prop <|
      lmI "motive" andRecMotive <|
      lm "intro" andRecMinor <|
      lm "left" (bv 3) <|
      lm "right" (bv 3) <|
      ap2 (bv 2) (bv 1) (bv 0)]]

/-- Twin of `andPinNames`. -/
def andPinNames : List Name := [andName, andIntroName, andRecName]

/-! ## Comparison -/

/-- Twin of `BasisKind`. -/
inductive BasisKind where
  | eqK | natK | emptyK | falseK

/-- Twin of `BasisKind.decls`. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .emptyK => emptyBasis
  | .falseK => falseBasis

/-- Twin of `ConstantInfo.atLps` (on core's `ConstantInfo`, no dot notation): a pin at the level-parameter names `ps`
(positionally). -/
def ciAtLps (ci : ConstantInfo) (ps : List Name) : ConstantInfo :=
  let lps := ci.levelParams
  let us := ps.map Level.param
  let at_ (e : Expr) : Expr := e.instLvlParamsI lps us
  match ci with
  | .inductInfo v => .inductInfo { v with levelParams := ps, type := at_ v.type }
  | .ctorInfo v => .ctorInfo { v with levelParams := ps, type := at_ v.type }
  | .recInfo v =>
    .recInfo { v with levelParams := ps, type := at_ v.type,
                      rules := v.rules.map fun rl => { rl with rhs := at_ rl.rhs } }
  | ci => ci

/-- Twin of `pinAgrees`: names and types (up to `mdata` and binder names and
infos), and the counts con-leche's records carry; an inductive has no
capabilities to compare. -/
def pinAgrees : ConstantInfo → ConstantInfo → Bool
  | .inductInfo v, .inductInfo v' => v.name == v'.name && Expr.clEq v.type v'.type
  | .ctorInfo v, .ctorInfo v' =>
    v.name == v'.name && Expr.clEq v.type v'.type &&
      v.numParams == v'.numParams && v.numFields == v'.numFields && v.induct == v'.induct
  | .recInfo v, .recInfo v' =>
    v.name == v'.name && Expr.clEq v.type v'.type &&
      majorIdxOf v == majorIdxOf v' && rulePrefixOf v == rulePrefixOf v' && v.k == v'.k &&
      v.rules.length == v'.rules.length &&
      (v.rules.zip v'.rules).all fun (r, r') =>
        r.ctor == r'.ctor && r.nfields == r'.nfields && Expr.clEq r.rhs r'.rhs
  | _, _ => false

/-- Twin of `pinCopyOk`. -/
def pinCopyOk (ci pin : ConstantInfo) : Bool :=
  let ps := ci.levelParams
  namesNodup ps && ps.length == pin.levelParams.length && pinAgrees ci (ciAtLps pin ps)

/-- Twin of `pinLinkOk`. -/
def pinLinkOk (R Rp : List Name) (C Cp : List Name) : Bool :=
  C.map Level.param == Cp.map fun p => (Level.param p).instantiateParams Rp (R.map Level.param)

/-- Twin of `constNamed?`. -/
def constNamed? (cs : List ConstantInfo) (n : Name) : Option ConstantInfo :=
  cs.find? fun c => c.name == n

/-- Twin of `blockLinksOk`. -/
def blockLinksOk (block pins : List ConstantInfo) : Bool :=
  let former := (block.head?.map (·.levelParams)).getD []
  (List.zip block pins).all fun (c, p) =>
    match c, p with
    | .ctorInfo v, _ => v.levelParams == former
    | .recInfo v, .recInfo vp =>
      vp.rules.all fun rl =>
        match constNamed? block rl.ctor, constNamed? pins rl.ctor with
        | some C, some Cp =>
          pinLinkOk v.levelParams vp.levelParams C.levelParams Cp.levelParams
        | _, _ => false
    | _, _ => true

/-- Twin of `listBeqBy`. -/
def listBeqBy (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listBeqBy f as bs
  | _, _ => false

/-- Twin of `pinListOk`. -/
def pinListOk (block pins : List ConstantInfo) : Bool :=
  listBeqBy pinCopyOk block pins && blockLinksOk block pins

/-- Twin of `basisNameHit`. -/
def basisNameHit (block : List ConstantInfo) : Option BasisKind :=
  [BasisKind.eqK, .natK, .emptyK, .falseK].find? fun k =>
    k.decls.map (·.name) == block.map (·.name)

/-- Twin of `canonEqList`: the list compared with the pin up to the level
parameters' names (`pinCopyOk`, without the nodup test, which `andPinOk`'s
caller makes anyway). -/
def canonEqList (xs ys : List ConstantInfo) : Bool :=
  listBeqBy (fun x y => x.levelParams.length == y.levelParams.length &&
    pinAgrees x (ciAtLps y x.levelParams)) xs ys

/-- Twin of `andPinOk` at an inductive block. -/
def andPinOkBlock (block : List ConstantInfo) (nP : Nat) : Bool :=
  !(block.any fun c => andPinNames.contains c.name) ||
    (nP == 2 && canonEqList block andPin)

/-- Twin of `andPinOk`: a declaration naming `And`, `And.intro` or `And.rec`
is the pinned block.  An inductive declaration is tested on its generated
block (`andPinOkBlock`). -/
def andPinOk : Declaration → Bool
  | .inductDecl .. => true
  | .axiomDecl v => !andPinNames.contains v.name
  | .defnDecl v => !andPinNames.contains v.name
  | .thmDecl v => !andPinNames.contains v.name
  | .opaqueDecl v => !andPinNames.contains v.name
  | .quotDecl => true
  | .mutualDefnDecl vs => !vs.any fun v => andPinNames.contains v.name

end Lean.Kernel.InLean

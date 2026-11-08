/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Environment
public import Lean.Kernel.InLean.ExprOps

/-!
# InLean: modes, errors, names, levels

The fuel-free basics of con-leche's checker, ported onto
`Lean.Level`/`Lean.Name`: the mode (`ConLeche.Kernel.Env`'s
`CheckMode`), the error kinds (`CheckError`), the zero-ness datum
(`ConLeche.Kernel.PropWhen`) and the level operations
(`ConLeche.Kernel.Level`: `simplify`, the `leqCore` cascade,
`isEquiv`, `zeronessOf`, `substPW`).

Level metavariables never reach the kernel (`addDecl` rejects them up
front); the operations below treat an `mvar` like a parameter that is
equal only to itself.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## Mode -/

/-- Twin of `ConLeche.CheckMode`: verified (the certificate families
run) or trusted (they do not).  The official kernel's `eagerReduce` flag
is a separate `Bool`, as in con-leche. -/
inductive CheckMode where
  | verified
  | trusted
  deriving Inhabited, BEq, Repr

/-- Twin of `CheckMode.verifiedChecks`. -/
@[inline] def CheckMode.verifiedChecks : CheckMode → Bool
  | .verified => true
  | .trusted => false

/-! ## Errors -/

/-- Twin of `ConLeche.CheckError`: `invalid` is a reject (the official
kernel rejects too), `notImplemented` a positively detected unsupported
feature (a decline), `internal` an error of unclear cause. -/
inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Inhabited

/-- The message `addDecl` reports, prefixed `(InLean)`. -/
def CheckError.toString : CheckError → String
  | .invalid m => s!"(InLean) {m}"
  | .notImplemented m => s!"(InLean) declined: {m}"
  | .internal m => s!"(InLean) internal error: {m}"

/-- Twin of `ConLeche.CheckM`. -/
abbrev CheckM := Except CheckError

/-! ## The zero-ness datum (twin of `ConLeche.PropWhen`) -/

inductive PropWhen where
  | never
  | ifAllZero (ps : List Name)
  deriving Inhabited

namespace PropWhen

@[inline] def isNever : PropWhen → Bool
  | .never => true
  | .ifAllZero _ => false

/-- Twin of `PropWhen.isProp` (`ConLeche.Kernel.PropRead`). -/
@[inline] def isProp : PropWhen → Bool
  | .ifAllZero [] => true
  | _ => false

def inter : PropWhen → PropWhen → PropWhen
  | .never, _ => .never
  | .ifAllZero _, .never => .never
  | .ifAllZero ps, .ifAllZero qs => .ifAllZero (ps ++ qs)

def bindZ.go (f : Name → PropWhen) : List Name → PropWhen
  | [] => .ifAllZero []
  | n :: rest => (f n).inter (go f rest)

def bindZ (f : Name → PropWhen) : PropWhen → PropWhen
  | .never => .never
  | .ifAllZero ps => bindZ.go f ps

end PropWhen

/-! ## Levels (twin of `ConLeche.Kernel.Level`) -/

namespace Lvl

def allParamsDefined (params : List Name) : Level → Bool
  | .zero => true
  | .succ l => allParamsDefined params l
  | .max l r | .imax l r => allParamsDefined params l && allParamsDefined params r
  | .param n => params.contains n
  | .mvar _ => false

def combining : Level → Level → Level
  | .zero, r => r
  | l, .zero => l
  | .succ l, .succ r => .succ (combining l r)
  | l, r => .max l r

def simplify : Level → Level
  | .zero => .zero
  | .param n => .param n
  | .mvar m => .mvar m
  | .succ l => .succ (simplify l)
  | .max l r => combining (simplify l) (simplify r)
  | .imax l r =>
    let ls := simplify l
    let rs := simplify r
    if ls == .zero || ls == .succ .zero then rs
    else match rs with
      | .zero => .zero
      | .succ _ => combining ls rs
      | _ => .imax ls rs

mutual
/-- Twin of `Level.leqCore`. -/
def leqCore (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if l == .zero ∧ diff ≥ 0 then some true
    else if r == .zero ∧ diff < 0 then some false
    else rest fuel l r diff

def rest (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .param a, .param x => some (a == x && diff ≥ 0)
  | .mvar a, .mvar x => some (a == x && diff ≥ 0)
  | .param _, .zero => some false
  | .zero, .param _ => some (diff ≥ 0)
  | .succ s, _ => leqCore fuel s r (diff - 1)
  | _, .succ s => leqCore fuel l s (diff + 1)
  | .max a b, _ => do
    if ← leqCore fuel a r diff then leqCore fuel b r diff else pure false
  | .param _, .max x y => do
    if ← leqCore fuel l x diff then pure true else leqCore fuel l y diff
  | .zero, .max x y => do
    if ← leqCore fuel l x diff then pure true else leqCore fuel l y diff
  | _, _ =>
    match l, r with
    | .imax a b, .imax x y =>
      if a == x && b == y && diff ≥ 0 then some true else imaxRules fuel l r diff
    | _, _ => imaxRules fuel l r diff

def imaxRules (fuel : Nat) (l r : Level) (diff : Int) : Option Bool :=
  match l, r with
  | .imax _ (.param p), _ => byCases fuel p l r diff
  | _, .imax _ (.param p) => byCases fuel p l r diff
  | .imax a (.imax x y), _ => leqCore fuel (.max (.imax a y) (.imax x y)) r diff
  | .imax a (.max x y), _ => leqCore fuel (simplify (.max (.imax a x) (.imax a y))) r diff
  | _, .imax x (.imax j k) => leqCore fuel l (.max (.imax x k) (.imax j k)) diff
  | _, .imax x (.max j k) => leqCore fuel l (simplify (.max (.imax x j) (.imax x k))) diff
  | _, _ => none

def byCases (fuel : Nat) (p : Name) (l r : Level) (diff : Int) : Option Bool := do
  let l0 := simplify (subst [p] [.zero] l)
  let r0 := simplify (subst [p] [.zero] r)
  if ← leqCore fuel l0 r0 diff then
    let ls := simplify (subst [p] [.succ (.param p)] l)
    let rs := simplify (subst [p] [.succ (.param p)] r)
    leqCore fuel ls rs diff
  else pure false
end

def defaultFuel : Nat := 10000

def leq (l r : Level) : Option Bool :=
  leqCore defaultFuel (simplify l) (simplify r) 0

/-- Twin of `Level.isEquiv`. -/
def isEquiv (l r : Level) : Option Bool := do
  if l == r then pure true
  else if simplify l == simplify r then pure true
  else if ← leq l r then leq r l else pure false

/-- Twin of `Level.zeronessOf`. -/
def zeronessOf : Level → PropWhen
  | .zero => .ifAllZero []
  | .succ _ => .never
  | .param n => .ifAllZero [n]
  | .mvar _ => .ifAllZero []
  | .max a b => (zeronessOf a).inter (zeronessOf b)
  | .imax _ b => zeronessOf b

/-- Twin of `Level.substPW`. -/
def substPW (ks : List Name) (vs : List Level) (pw : PropWhen) : PropWhen :=
  pw.bindZ fun n => zeronessOf (substGo ks vs n)

/-- `isEquiv u 0 = some true`. -/
@[inline] def isZero (u : Level) : Bool := isEquiv u .zero == some true

/-- Twin of `Level.isAlwaysZero`. -/
def isAlwaysZero (s : Level) : Bool :=
  match zeronessOf s with
  | .ifAllZero [] => true
  | _ => false

/-- Twin of `Level.zeroWhereZero`. -/
def zeroWhereZero (s u : Level) : Bool :=
  match zeronessOf s, zeronessOf u with
  | .never, _ => true
  | .ifAllZero _, .never => false
  | .ifAllZero ps, .ifAllZero qs => qs.all ps.contains

end Lvl

/-- Twin of `Name.nodup`. -/
def namesNodup : List Name → Bool
  | [] => true
  | n :: ns => !ns.contains n && namesNodup ns

/-! ## Names the checker reads -/

def natName : Name := `Nat
def natZeroName : Name := `Nat.zero
def natSuccName : Name := `Nat.succ
def natPredName : Name := `Nat.pred
def natAddName : Name := `Nat.add
def natSubName : Name := `Nat.sub
def natMulName : Name := `Nat.mul
def natPowName : Name := `Nat.pow
def natBeqName : Name := `Nat.beq
def natBleName : Name := `Nat.ble
def natDivName : Name := `Nat.div
def natModName : Name := `Nat.mod
def natGcdName : Name := `Nat.gcd
def natLandName : Name := `Nat.land
def natLorName : Name := `Nat.lor
def natXorName : Name := `Nat.xor
def natShiftLeftName : Name := `Nat.shiftLeft
def natShiftRightName : Name := `Nat.shiftRight
def boolName : Name := `Bool
def boolTrueName : Name := `Bool.true
def boolFalseName : Name := `Bool.false
def eagerReduceName : Name := `eagerReduce
def stringName : Name := `String
def stringOfListName : Name := `String.ofList
def listName : Name := `List
def listNilName : Name := `List.nil
def listConsName : Name := `List.cons
def charName : Name := `Char
def charOfNatName : Name := `Char.ofNat
def andName : Name := `And
def andIntroName : Name := `And.intro
def eqName : Name := `Eq
def eqReflName : Name := `Eq.refl
def eqRecName : Name := `Eq.rec
def quotName : Name := `Quot
def quotMkName : Name := `Quot.mk
def quotLiftName : Name := `Quot.lift
def quotIndName : Name := `Quot.ind
def quotSoundName : Name := `Quot.sound
def sorryAxName : Name := `sorryAx

/-- Twin of `natOpNames`. -/
def natOpNames : List Name :=
  [natPredName, natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName]

/-- Twin of `natDivModNames` (= `natOpWfNames`). -/
def natDivModNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName]

/-- Twin of `reservedBasisNames` (`ConLeche.Kernel.Basis.Names`):
the pinned basis blocks' constants. -/
def reservedBasisNames : List Name :=
  [`Eq, `Eq.refl, `Eq.rec, `Nat, `Nat.zero, `Nat.succ, `Nat.rec,
   `Empty, `Empty.rec, `False, `False.rec,
   `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound]

end Lean.Kernel.InLean

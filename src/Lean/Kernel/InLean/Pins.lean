/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Basic

/-!
# InLean: the pinned shapes

Twins of con-leche's hand-written pins, spelled with the
same builder (`ConLeche/Kernel/Basis/Builder.lean`), now producing
`Lean.Expr`: the quotient block (`Basis/Quot.lean`), the `Nat` and `Bool`
types (`Basis/Nat.lean`), the standard axioms
(`StdAxioms.lean`), the compiler-trust family (`TrustAxioms.lean`,
`TrustPins.lean`) and the Nat operations' certificate statements
(`natOpEquations`, `divModCertStmts`, `Checker.lean`).  A pin is compared
with Lean's constant by `==`, alpha-equivalence (binder names and infos
ignored), so the builder's binder names are for display only.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace BasisDSL

def bn (s : String) : Name := .str .anonymous s
def uN : Name := bn "u"
def u : Level := .param uN
def vN : Name := bn "v"
def v : Level := .param vN
def u1N : Name := bn "u_1"
def u1 : Level := .param u1N
def bv (i : Nat) : Expr := .bvar i
def srt (u : Level) : Expr := .sort u
def prop : Expr := .sort .zero
def type1 : Expr := .sort (.succ .zero)
def cnst (n : Name) (us : List Level := []) : Expr := .const n us
def pi (x : String) (ty body : Expr) : Expr := .forallE (bn x) ty body .default
def piI (x : String) (ty body : Expr) : Expr := .forallE (bn x) ty body .implicit
def piA (ty body : Expr) : Expr := .forallE `a ty body .default
def lm (x : String) (ty body : Expr) : Expr := .lam (bn x) ty body .default
def lmI (x : String) (ty body : Expr) : Expr := .lam (bn x) ty body .implicit
def ap2 (f a b : Expr) : Expr := .app (.app f a) b
def ap3 (f a b c : Expr) : Expr := .app (.app (.app f a) b) c
def ap4 (f a b c d : Expr) : Expr := .app (.app (.app (.app f a) b) c) d

end BasisDSL

open BasisDSL

/-- A pinned constant: name, level parameters, type. -/
structure Pin where
  name : Name
  lps : List Name
  type : Expr

/-- `e` without `mdata` nodes (a memoised DAG walk per level of
nesting; pins and the types compared with them are small).  con-leche's
frontend drops `mdata` at parse; Lean's stored types carry it (the
`borrowed` annotations of `Nat.add`'s domains). -/
def stripMData (e : Expr) : Expr := EO.stripMData e

/-- A type at the pin's level-parameter names (positionally), `mdata`
stripped: con-leche's `ConstantVal.canon` comparison (the pinned basis
blocks are matched up to level-parameter renaming). -/
def canonAt (lps pinLps : List Name) (ty : Expr) : Expr :=
  stripMData (if lps == pinLps then ty else ty.instLvlParamsI lps (pinLps.map .param))

/-- Twin of `ConstantVal.matchesPin` up to `canon`. -/
def Pin.matches (p : Pin) (ci : ConstantInfo) : Bool :=
  ci.name == p.name && ci.levelParams.length == p.lps.length &&
    EO.alphaEq (canonAt ci.levelParams p.lps ci.type) p.type

/-- `Pin.matches` on a declaration's own name, levels and type. -/
def Pin.matchesDecl (p : Pin) (n : Name) (lps : List Name) (ty : Expr) : Bool :=
  n == p.name && lps.length == p.lps.length && EO.alphaEq (canonAt lps p.lps ty) p.type

/-! ## The `Nat` and `Bool` types the guards look up (the basis blocks are
`Lean/Kernel/InLean/Inductives/Basis.lean`'s) -/

def natPin : Pin := ⟨natName, [], type1⟩
def boolPin : Pin := ⟨boolName, [], type1⟩

/-! ## The quotient block (twin of `Basis/Quot.lean`) -/

def quotRel : Expr := piA (bv 0) (piA (bv 1) prop)

def quotPin : Pin := ⟨quotName, [uN], piI "α" (srt u) <| pi "r" quotRel (srt u)⟩

def quotMkPin : Pin := ⟨quotMkName, [uN],
  piI "α" (srt u) <| pi "r" quotRel <| pi "a" (bv 1) (ap2 (cnst quotName [u]) (bv 2) (bv 1))⟩

def quotLiftF : Expr := pi "a" (bv 2) (bv 1)

def quotLiftH : Expr :=
  pi "a" (bv 3) <|
  pi "b" (bv 4) <|
  pi "a" (ap2 (bv 4) (bv 1) (bv 0)) <|
  ap3 (cnst eqName [v]) (bv 4) (.app (bv 3) (bv 2)) (.app (bv 3) (bv 1))

def quotLiftPin : Pin := ⟨quotLiftName, [uN, vN],
  piI "α" (srt u) <| piI "r" quotRel <| piI "β" (srt v) <|
  pi "f" quotLiftF <| pi "a" quotLiftH <|
  pi "a" (ap2 (cnst quotName [u]) (bv 4) (bv 3)) (bv 3)⟩

/-- `Quot.lift`'s rule over `Quot.mk` (the pinned block's recursor rule). -/
def quotLiftRule : Expr :=
  lm "α" (srt u) <| lm "r" quotRel <| lm "β" (srt v) <| lm "f" quotLiftF <|
  lm "h" quotLiftH <| lm "a" (bv 4) (.app (bv 2) (bv 0))

def quotIndMotive : Expr := pi "a" (ap2 (cnst quotName [u]) (bv 1) (bv 0)) prop

def quotIndMk : Expr :=
  pi "a" (bv 2) <| .app (bv 1) (ap3 (cnst quotMkName [u]) (bv 3) (bv 2) (bv 0))

def quotIndPin : Pin := ⟨quotIndName, [uN],
  piI "α" (srt u) <| piI "r" quotRel <| piI "β" quotIndMotive <|
  pi "mk" quotIndMk <| pi "q" (ap2 (cnst quotName [u]) (bv 3) (bv 2)) (.app (bv 2) (bv 0))⟩

def quotIndRule : Expr :=
  lm "α" (srt u) <| lm "r" quotRel <| lm "β" quotIndMotive <| lm "mk" quotIndMk <|
  lm "a" (bv 3) (.app (bv 1) (bv 0))

def quotSoundPin : Pin := ⟨quotSoundName, [uN],
  piI "α" (srt u) <| piI "r" quotRel <| piI "a" (bv 1) <| piI "b" (bv 2) <|
  piA (ap2 (bv 2) (bv 1) (bv 0)) <|
  ap3 (cnst eqName [u]) (ap2 (cnst quotName [u]) (bv 4) (bv 3))
    (ap3 (cnst quotMkName [u]) (bv 4) (bv 3) (bv 2))
    (ap3 (cnst quotMkName [u]) (bv 4) (bv 3) (bv 1))⟩

/-! ## The standard axioms (twin of `StdAxioms.lean`) -/

def propextName : Name := `propext
def choiceName : Name := `Classical.choice
def iffName : Name := `Iff
def iffIntroName : Name := `Iff.intro
def iffRecName : Name := `Iff.rec
def nonemptyName : Name := `Nonempty
def nonemptyIntroName : Name := `Nonempty.intro
def nonemptyRecName : Name := `Nonempty.rec

def iffPin : Pin := ⟨iffName, [], pi "a" prop <| pi "b" prop prop⟩
def iffIntroPin : Pin := ⟨iffIntroName, [],
  pi "a" prop <| pi "b" prop <| pi "mp" (piA (bv 1) (bv 1)) <| pi "mpr" (piA (bv 1) (bv 3)) <|
  ap2 (cnst iffName) (bv 3) (bv 2)⟩
def iffRecIntro : Expr :=
  pi "mp" (pi "right" (bv 2) (bv 2)) <| pi "mpr" (piA (bv 2) (bv 4)) <|
  .app (bv 2) (ap4 (cnst iffIntroName) (bv 4) (bv 3) (bv 1) (bv 0))
def iffRecPin : Pin := ⟨iffRecName, [uN],
  pi "a" prop <| pi "b" prop <|
  pi "motive" (pi "t" (ap2 (cnst iffName) (bv 1) (bv 0)) (srt u)) <|
  pi "intro" iffRecIntro <|
  pi "t" (ap2 (cnst iffName) (bv 3) (bv 2)) (.app (bv 2) (bv 0))⟩
def propextPin : Pin := ⟨propextName, [],
  pi "a" prop <| pi "b" prop <| piA (ap2 (cnst iffName) (bv 1) (bv 0)) <|
  ap3 (cnst eqName [.succ .zero]) prop (bv 2) (bv 1)⟩
def nonemptyPin : Pin := ⟨nonemptyName, [uN], pi "α" (srt u) prop⟩
def nonemptyIntroPin : Pin := ⟨nonemptyIntroName, [uN],
  pi "α" (srt u) <| pi "val" (bv 0) <| .app (cnst nonemptyName [u]) (bv 1)⟩
def nonemptyRecPin : Pin := ⟨nonemptyRecName, [uN],
  pi "α" (srt u) <|
  pi "motive" (pi "t" (.app (cnst nonemptyName [u]) (bv 0)) prop) <|
  pi "intro" (pi "val" (bv 1) <| .app (bv 1) (ap2 (cnst nonemptyIntroName [u]) (bv 2) (bv 0))) <|
  pi "t" (.app (cnst nonemptyName [u]) (bv 2)) (.app (bv 2) (bv 0))⟩
def choicePin : Pin := ⟨choiceName, [uN],
  pi "α" (srt u) <| piA (.app (cnst nonemptyName [u]) (bv 0)) (bv 1)⟩

/-! ## The compiler-trust family (twin of `TrustAxioms.lean`/`TrustPins.lean`) -/

def trueName : Name := `True
def trueIntroName : Name := `True.intro
def trustCompilerName : Name := `Lean.trustCompiler
def reduceNatName : Name := `Lean.reduceNat
def reduceBoolName : Name := `Lean.reduceBool
def ofReduceNatName : Name := `Lean.ofReduceNat
def ofReduceBoolName : Name := `Lean.ofReduceBool
def reduceOpNames : List Name := [reduceNatName, reduceBoolName]

def ofReduceOp (n : Name) : Name :=
  if n == ofReduceNatName then reduceNatName else reduceBoolName

def truePin : Pin := ⟨trueName, [], .sort .zero⟩
def trueIntroPin : Pin := ⟨trueIntroName, [], .const trueName []⟩
def trustCompilerPin : Pin := ⟨trustCompilerName, [], .const trueName []⟩

def reduceElemTy (c : Name) : Expr :=
  if c == reduceNatName then .const natName [] else .const boolName []

def reduceOpPin (c : Name) : Pin := ⟨c, [], pi "n" (reduceElemTy c) (reduceElemTy c)⟩

def ofReducePin (n : Name) : Pin :=
  let c := ofReduceOp n
  let τ := reduceElemTy c
  let eqApp : Expr → Expr → Expr := fun x y => ap3 (cnst eqName [.succ .zero]) τ x y
  ⟨n, [], pi "a" τ <| pi "b" τ <| pi "h" (eqApp (.app (cnst c) (bv 1)) (bv 0)) (eqApp (bv 2) (bv 1))⟩

/-- Twin of `reduceDeclPin`: the identity on the element type. -/
def reduceDeclPin (c : Name) : Expr :=
  if c == reduceNatName then lm "n" (cnst natName) (bv 0) else lm "b" (cnst boolName) (bv 0)

/-- Twin of `nonStdAxiomMsg`. -/
def nonStdAxiomMsg (n : Name) : String :=
  let tac? : Option String := match n with
    | .str (.str (.str _ "_native") tac) ax =>
      if ax.startsWith "ax" then
        some (if tac == "decide" then "decide +native" else (Name.str .anonymous tac).toString)
      else none
    | _ => none
  match tac? with
  | some tac =>
    s!"non-standard axiom ({n}), apparently added by the `{tac}` tactic; \
      con-leche does not support such axioms at the moment"
  | none => s!"non-standard axiom ({n}); con-leche does not support such axioms at the moment"

/-! ## The Nat operations' certificate statements -/

/-- Twin of `natOpDeps`. -/
def natOpDeps (c : Name) : List Name :=
  if c == natPredName then [natPredName]
  else if c == natAddName then [natAddName]
  else if c == natSubName then [natPredName, natSubName]
  else if c == natMulName then [natAddName, natMulName]
  else if c == natPowName then [natAddName, natMulName, natPowName]
  else if c == natBeqName then [natBeqName]
  else if c == natBleName then [natBleName]
  else if c == natDivName then [natPredName, natSubName, natBleName, natDivName]
  else if c == natModName then [natPredName, natSubName, natBleName, natModName]
  else if c == natGcdName then [natBleName, natModName, natGcdName]
  else if c == natLandName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natLandName]
  else if c == natLorName then
    [natAddName, natSubName, natMulName, natBleName, natDivName, natModName, natLorName]
  else if c == natXorName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natXorName]
  else if c == natShiftLeftName then
    [natSubName, natMulName, natBleName, natShiftLeftName]
  else if c == natShiftRightName then
    [natSubName, natBleName, natDivName, natShiftRightName]
  else []

/-- Twin of `natOpEquations`, over the two free variables `x`, `y`
(con-leche's `fvar d`/`fvar (d+1)` of type `Nat`). -/
def natOpEquations (x y : Expr) (c : Name) : List (Expr × Expr) :=
  let z : Expr := .const natZeroName []
  let s : Expr → Expr := (.app (.const natSuccName []) ·)
  let ap1 : Name → Expr → Expr := fun n a => .app (.const n []) a
  let ap2' : Name → Expr → Expr → Expr := fun n a b => .app (.app (.const n []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  if c == natPredName then [(ap1 c z, z), (ap1 c (s x), x)]
  else if c == natAddName then [(ap2' c x z, x), (ap2' c x (s y), s (ap2' c x y))]
  else if c == natSubName then [(ap2' c x z, x), (ap2' c x (s y), ap1 natPredName (ap2' c x y))]
  else if c == natMulName then [(ap2' c x z, z), (ap2' c x (s y), ap2' natAddName (ap2' c x y) x)]
  else if c == natPowName then [(ap2' c x z, s z), (ap2' c x (s y), ap2' natMulName (ap2' c x y) x)]
  else if c == natBeqName then
    [(ap2' c z z, bT), (ap2' c z (s y), bF), (ap2' c (s x) z, bF), (ap2' c (s x) (s y), ap2' c x y)]
  else if c == natBleName then
    [(ap2' c z y, bT), (ap2' c (s x) z, bF), (ap2' c (s x) (s y), ap2' c x y)]
  else []

/-- Twin of `divModCertStmts`, over the two free variables `x`, `y`:
per certificate, its hypotheses and its equation. -/
def divModCertStmts (x y : Expr) (c : Name) : List (List Expr × Expr) :=
  let natTy : Expr := .const natName []
  let one : Expr := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr → Expr → Expr := fun a b => .app (.app (.const natBleName []) a) b
  let eqB : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr → Expr → Expr := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr → Expr → Expr := fun a b => .app (.app (.const natSubName []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  let z : Expr := .const natZeroName []
  let two : Expr := .app (.const natSuccName []) one
  let mod2 : Expr → Expr → Expr := fun a b => .app (.app (.const natModName []) a) b
  let div2 : Expr → Expr → Expr := fun a b => .app (.app (.const natDivName []) a) b
  let add2 : Expr → Expr → Expr := fun a b => .app (.app (.const natAddName []) a) b
  let mul2 : Expr → Expr → Expr := fun a b => .app (.app (.const natMulName []) a) b
  if c == natGcdName then
    [([eqB (ble2 one x) bT], eqN (op2 x y) (op2 (mod2 y x) x)),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c == natShiftLeftName then
    [([eqB (ble2 one y) bT], eqN (op2 x y) (op2 (mul2 two x) (sub2 y one))),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c == natShiftRightName then
    [([eqB (ble2 one y) bT], eqN (op2 x y) (div2 (op2 x (sub2 y one)) two)),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c == natLandName then
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two)))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) z)]
  else if c == natLorName then
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two)) (mul2 (mod2 x two) (mod2 y two))))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c == natXorName then
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else
  let recRhs : Expr :=
    if c == natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr := if c == natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]

/-- Twin of `Expr.substConst0`: replace the level-free constant `n` by
`r` along the application spine (no binders). -/
def substConst0 (n : Name) (r : Expr) : Expr → Expr
  | .const c [] => if c == n then r else .const c []
  | .app f a => .app (substConst0 n r f) (substConst0 n r a)
  | e => e

/-- Twin of `Expr.substConstAll`: replace the level-free constant `n` by
the closed `r` everywhere (a memoised DAG walk, `Expr.replace`). -/
def substConstAll (n : Name) (r : Expr) (e : Expr) : Expr :=
  e.replaceI fun
    | .const c [] => if c == n then some r else none
    | _ => none

end Lean.Kernel.InLean

import Lean

open Lean Meta

def mkToCtorIdx' (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let us := info.levelParams.map mkLevelParam
  let e := mkConst (mkCasesOnName indName) (1::us)
  let t ← inferType e
  let e ← forallBoundedTelescope t info.numParams fun xs t => do
    let e := mkAppN e xs
    let motive ← forallTelescope (← whnfD t).bindingDomain! fun ys _ =>
      mkLambdaFVars ys (mkConst ``Nat)
    let t ← instantiateForall t #[motive]
    let e := mkApp e motive
    let e ← forallBoundedTelescope t (some (info.numIndices + 1)) fun ys t => do
      let e := mkAppN e ys
      let e ← forallBoundedTelescope t info.numCtors fun alts _ => do
        let alts' ← alts.mapIdxM fun i alt => do
          let altType ← inferType alt
          forallTelescope altType fun zs _ =>
            mkLambdaFVars zs (mkNatLit i)
        return mkAppN e alts'
      mkLambdaFVars ys e
    mkLambdaFVars xs e

  let declName := indName ++ `toCtorIdx'
  addAndCompile <| Declaration.defnDecl {
    name        := declName
    levelParams := info.levelParams
    type        := (← inferType e)
    value       := e
    safety      := DefinitionSafety.safe
    hints       := ReducibilityHints.abbrev
  }
  setReducibleAttribute declName

def mkNatLookupTable (n : Expr) (es : Array Expr) (default : Expr) : MetaM Expr := do
  let type ← inferType default
  let u ← getLevel type
  let mut acc := default
  for i in (Array.range es.size).reverse do
    let e := es[i]!
    acc := mkApp4 (mkConst ``cond [u]) type (← mkAppM ``Nat.beq #[n, mkNatLit i]) e acc
  return acc

def mkWithCtorType (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let us := info.levelParams.map mkLevelParam
  let v ← pure `v -- TODO: mkFreshUserName `v
  let indTyCon := mkConst indName us
  let indTyKind ← inferType indTyCon
  let indLevel ← getDecLevel indTyKind
  let e ← forallBoundedTelescope indTyKind info.numParams fun xs  _ => do
    withLocalDeclD `P (mkSort (mkLevelParam v).succ) fun P => do
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
      let default ← mkArrow (mkConst ``PUnit [indLevel]) P
      let es ← info.ctors.toArray.mapM fun ctorName => do
        let ctor := mkAppN (mkConst ctorName us) xs
        let ctorType ← inferType ctor
        let argType ← forallTelescope ctorType fun ys _ =>
          mkForallFVars ys P
        mkArrow (mkConst ``PUnit [indLevel]) argType
      let e ← mkNatLookupTable ctorIdx es default
      mkLambdaFVars ((xs.push P).push ctorIdx) e

  let declName := indName ++ `withCtorType
  addAndCompile <| Declaration.defnDecl {
    name        := declName
    levelParams := v :: info.levelParams
    type        := (← inferType e)
    value       := e
    safety      := DefinitionSafety.safe
    hints       := ReducibilityHints.abbrev
  }
  setReducibleAttribute declName

def mkWithCtor (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let withCtorTypeName := indName ++ `withCtorType
  let us := info.levelParams.map mkLevelParam
  let v ← pure `v -- TODO: mkFreshUserName `v
  let indTyCon := mkConst indName us
  let indTyKind ← inferType indTyCon
  let indLevel ← getDecLevel indTyKind
  let e ← forallBoundedTelescope indTyKind info.numParams fun xs t => do
    withLocalDeclD `P (mkSort (mkLevelParam v).succ) fun P => do
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
      let withCtorTypeNameApp := mkAppN (mkConst withCtorTypeName (mkLevelParam v :: us)) (xs.push P)
      let kType := mkApp withCtorTypeNameApp  ctorIdx
      withLocalDeclD `k kType fun k =>
      withLocalDeclD `k' P fun k' =>
      forallBoundedTelescope t info.numIndices fun ys t' => do
        assert! t'.isSort
        withLocalDeclD `x (mkAppN indTyCon (xs ++ ys)) fun x => do
          let e := mkConst (mkCasesOnName indName) (.succ (mkLevelParam v)::us)
          let e := mkAppN e xs
          let motive ← mkLambdaFVars (ys.push x) P
          let e := mkApp e motive
          let e := mkAppN e ys
          let e := mkApp e x
          let alts ← info.ctors.toArray.mapIdxM fun i ctorName => do
            let ctor := mkAppN (mkConst ctorName us) xs
            let ctorType ← inferType ctor
            forallTelescope ctorType fun zs _ => do
              let heq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) ctorIdx (mkNatLit i)
              let «then» ← withLocalDeclD `h heq fun h => do
                let e ← mkEqNDRec (motive := withCtorTypeNameApp) k h
                let e := mkApp e (mkConst ``PUnit.unit [indLevel])
                let e := mkAppN e zs
                -- ``Eq.ndrec
                mkLambdaFVars #[h] e
              let «else» ← withLocalDeclD `h (mkNot heq) fun h =>
                mkLambdaFVars #[h] k'
              let alt := mkApp5 (mkConst ``dite [(mkLevelParam v).succ])
                  P heq (mkApp2 (mkConst ``Nat.decEq) ctorIdx (mkNatLit i))
                  «then» «else»
              mkLambdaFVars zs alt
          let e := mkAppN e alts
          mkLambdaFVars (xs ++ #[P, ctorIdx, k, k'] ++ ys ++ #[x]) e


  let declName := indName ++ `withCtor
  addDecl <| Declaration.defnDecl {
    name        := declName
    levelParams := v :: info.levelParams
    type        := (← inferType e)
    value       := e
    safety      := DefinitionSafety.safe
    hints       := ReducibilityHints.abbrev
  }
  setReducibleAttribute declName


inductive Vec.{u} (α : Type) : Nat → Type u where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)


run_meta do mkToCtorIdx' `Vec
run_meta do mkWithCtorType `Vec
run_meta do mkWithCtor `Vec

/--
info: @[reducible] def Vec.toCtorIdx'.{u} : {α : Type} → {a : Nat} → Vec α a → Nat :=
fun {α} {a} t => Vec.casesOn t 0 fun {n} a a => 1
-/
#guard_msgs in
#print Vec.toCtorIdx'

/--
info: @[reducible] def Vec.withCtorType.{v, u} : Type → Type v → Nat → Type (max u v) :=
fun α P ctorIdx =>
  bif Nat.beq ctorIdx 0 then PUnit.{u + 1} → P
  else bif Nat.beq ctorIdx 1 then PUnit.{u + 1} → {n : Nat} → α → Vec.{u} α n → P else PUnit.{u + 1} → P
-/
#guard_msgs in
set_option pp.universes true in
#print Vec.withCtorType

/--
info: @[reducible] def Vec.withCtor.{v, u} : (α : Type) →
  (P : Type v) → (ctorIdx : Nat) → Vec.withCtorType α P ctorIdx → P → (a : Nat) → Vec α a → P :=
fun α P ctorIdx k k' a x =>
  Vec.casesOn x (if h : ctorIdx = 0 then (h ▸ k) PUnit.unit else k') fun {n} a a_1 =>
    if h : ctorIdx = 1 then (h ▸ k) PUnit.unit a a_1 else k'
-/
#guard_msgs in
#print Vec.withCtor

abbrev Vec.CtorIdx := Nat

def Vec.ctorIdx : Vec α n → Vec.CtorIdx
  | .nil => 0
  | .cons .. => 1

/--
Helper definition to determine the type of the success callback of `Vec.withCtor`:

The `PUnit` argument is necessary to lift to the right universe. Could use `ULift` as well,
but this makes the construction more self-contained.

Cannot eliminate into `Sort` due to (likely) #7096.
-/
def Vec.withCtorType'.{u,v} (α : Type) (idx : CtorIdx) (P : Type u) : Type (max v u) :=
  bif idx.beq 0 then
    PUnit.{v+1} → P
  else bif idx.beq 1 then
    PUnit.{v+1} → {n : Nat} → α → Vec.{v} α n → P
  else
    PUnit.{v+1} → P

/--
`Vec.withCon idx k k' v` checks if `v` has constructor `idx`.
If yes, passes the constructor's fields to `k`.
If not, returns `k'`
-/
noncomputable -- avoid old code generator bug #1774
def Vec.withCtor'.{u,v} (α : Type) (P : Type u) (idx : CtorIdx)
    (k : Vec.withCtorType.{u,v} α P idx) (k' : P) (n : Nat) : Vec.{v} α n → P
  | .nil =>
    if h : idx = 0 then
      (h ▸ k :) PUnit.unit
    else
      k'
  | .cons x xs =>
    if h : idx = 1 then
      (h ▸ k :) PUnit.unit x xs
    else
      k'

noncomputable
def Vec.withNil.{u,v} {α : Type} {P : Type u}
    (k : P) (k' : P) {n : Nat} : Vec.{v} α n → P :=
  Vec.withCtor _ _ 0 (fun _ => k) k' _

noncomputable
def Vec.withCons.{u,v} {α : Type} {P : Type u}
    (k : (n : Nat) → (x : α) → (xs : Vec.{v} α n) → P) (k' : P) {n : Nat} : Vec α n → P :=
  Vec.withCtor _ _ 1 (fun _ => @k) k' _


def Vec.noConfusionType'.{u,v} {α : Type} {n : Nat} (P : Sort u) (v1 v2 : Vec.{v} α n) : Sort u :=
  v1.casesOn
    (nil := v2.withNil (P → P) P)
    (cons := fun {n} x xs => v2.withCons (fun n' x' xs' => (n = n' → x = x' → HEq xs xs' → P) → P) P)

-- Let’s check if our construction is equivalent to the existing one
example : @Vec.noConfusionType = @Vec.noConfusionType' := by
  ext α n P v1 v2;  cases v1 <;> cases v2 <;> rfl


-- inductive Enum.{u} : Type u where | a | b
-- set_option pp.universes true in
-- #print noConfusionTypeEnum

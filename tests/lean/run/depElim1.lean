import Lean.Meta.Match

open Lean
open Lean.Meta
open Lean.Meta.Match

/- Infrastructure for testing -/

universe u v

def check (x : Bool) : IO Unit := do
unless x do
  throw $ IO.userError "check failed"

def inaccessible {α : Sort u} (a : α) : α := a
def val {α : Sort u} (a : α) : α := a

inductive Pat {α : Sort u} (a : α) : Type u
| mk : Pat a

inductive ArrayLit0 (α : Sort u) : Type u | mk : ArrayLit0 α
inductive ArrayLit1 {α : Sort u} (a : α) : Type u | mk : ArrayLit1 a
inductive ArrayLit2 {α : Sort u} (a b : α) : Type u | mk : ArrayLit2 a b
inductive ArrayLit3 {α : Sort u} (a b c : α) : Type u | mk : ArrayLit3 a b c
inductive ArrayLit4 {α : Sort u} (a b c d : α) : Type u | mk : ArrayLit4 a b c d

private def getConstructorVal (ctorName : Name) (fn : Expr) (args : Array Expr) : MetaM (Option (ConstructorVal × Expr × Array Expr)) := do
let env ← getEnv
match env.find? ctorName with
| some (ConstantInfo.ctorInfo v) => if args.size == v.numParams + v.numFields then return some (v, fn, args) else return none
| _                              => return none

private def constructorApp? (e : Expr) : MetaM (Option (ConstructorVal × Expr × Array Expr)) := do
let env ← getEnv
match e with
| Expr.lit (Literal.natVal n) =>
   if n == 0 then getConstructorVal `Nat.zero (mkConst `Nat.zero) #[] else getConstructorVal `Nat.succ (mkConst `Nat.succ) #[mkNatLit (n-1)]
| _ =>
  let fn := e.getAppFn
  match fn with
  | Expr.const n _ => getConstructorVal n fn e.getAppArgs
  | _              => pure none

/- Convert expression using auxiliary hints `inaccessible` and `val` into a pattern -/
partial def mkPattern : Expr → MetaM Pattern
| e => do
  if e.isAppOfArity `val 2 then
    return Pattern.val e.appArg!
  else if e.isAppOfArity `inaccessible 2 then
    return Pattern.inaccessible e.appArg!
  else if e.isFVar then
    return Pattern.var e.fvarId!
  else if e.isAppOfArity `ArrayLit0 1 ||
          e.isAppOfArity `ArrayLit1 2 ||
          e.isAppOfArity `ArrayLit2 3 ||
          e.isAppOfArity `ArrayLit3 4 ||
          e.isAppOfArity `ArrayLit4 5 then
    let args := e.getAppArgs
    let type := args[0]!
    let ps   := args.extract 1 args.size
    let ps ← ps.toList.mapM mkPattern
    return Pattern.arrayLit type ps
  else match e.arrayLit? with
    | some (_, es) =>
      let pats ← es.mapM mkPattern
      let type ← inferType e
      let type ← whnfD type
      let elemType := type.appArg!
      return Pattern.arrayLit elemType pats
    | none =>
      let e ← whnfD e
      let r? ← constructorApp? e
      match r? with
      | none      => throwError "unexpected pattern"
      | some (cval, fn, args) =>
        let params := args.extract 0 cval.numParams
        let fields := args.extract cval.numParams args.size
        let pats ← fields.toList.mapM mkPattern
        return Pattern.ctor cval.name fn.constLevels! params.toList pats

partial def decodePats : Expr → MetaM (List Pattern)
| e => do
  match e.app2? `Pat with
  | some (_, pat) => let pat ← mkPattern pat; return [pat]
  | none =>
    match e.prod? with
    | none => throwError "unexpected pattern"
    | some (pat, pats) =>
      let pat  ← decodePats pat
      let pats ← decodePats pats
      return pat ++ pats

partial def decodeAltLHS (e : Expr) : MetaM AltLHS :=
forallTelescopeReducing e fun args body => do
  let decls ← args.toList.mapM (fun arg => getLocalDecl arg.fvarId!)
  let pats  ← decodePats body
  return { ref := Syntax.missing, fvarDecls := decls, patterns := pats }

partial def decodeAltLHSs : Expr → MetaM (List AltLHS)
| e => do
  match e.app2? `LHS with
  | some (_, lhs) => let lhs ← decodeAltLHS lhs; return [lhs]
  | none =>
    match e.prod? with
    | none => throwError "unexpected LHS"
    | some (lhs, lhss) =>
      let lhs  ← decodeAltLHSs lhs
      let lhss ← decodeAltLHSs lhss
      return lhs ++ lhss

def withDepElimFrom {α} (declName : Name) (numPats : Nat) (k : List FVarId → List AltLHS → MetaM α) : MetaM α := do
let cinfo ← getConstInfo declName
forallTelescopeReducing cinfo.type fun args body =>
  if args.size < numPats then
    throwError "insufficient number of parameters"
  else do
    let xs := (args.extract (args.size - numPats) args.size).toList.map $ Expr.fvarId!
    let alts ← decodeAltLHSs body
    k xs alts

inductive LHS {α : Sort u} (a : α) : Type u
| mk : LHS a

instance LHS.inhabited {α} (a : α) : Inhabited (LHS a) := ⟨LHS.mk⟩

-- set_option trace.Meta.debug true
-- set_option trace.Meta.Tactic.cases true
-- set_option trace.Meta.Tactic.subst true

@[init] def register : IO Unit :=
registerTraceClass `Meta.mkElim

/- Helper methods for testins mkElim -/

private def getUnusedLevelParam (majors : List Expr) (lhss : List AltLHS) : MetaM Level := do
let mut s := {}
for major in majors do
  let major ← instantiateMVars major
  let majorType ← inferType major
  let majorType ← instantiateMVars majorType
  s := collectLevelParams s major
  s := collectLevelParams s majorType
return s.getUnusedLevelParam

/- Return `Prop` if `inProf == true` and `Sort u` otherwise, where `u` is a fresh universe level parameter. -/
private def mkElimSort (majors : List Expr) (lhss : List AltLHS) (inProp : Bool) : MetaM Expr := do
if inProp then
  return mkSort levelZero
else
  let v ← getUnusedLevelParam majors lhss
  return mkSort $ v

def mkTester (elimName : Name) (majors : List Expr) (lhss : List AltLHS) (inProp : Bool := false) : MetaM MatcherResult := do
generalizeTelescope majors.toArray fun majors => do
  let resultType := if inProp then mkConst `True /- some proposition -/ else mkConst `Nat
  let matchType ← mkForallFVars majors resultType
  Match.mkMatcher { matcherName := elimName, matchType, discrInfos := mkArray majors.size {}, lhss }

def test (ex : Name) (numPats : Nat) (elimName : Name) (inProp : Bool := false) : MetaM Unit :=
withDepElimFrom ex numPats fun majors alts => do
  let majors := majors.map mkFVar
  trace[Meta.debug] m!"majors: {majors.toArray}"
  let r ← mkTester elimName majors alts inProp
  r.addMatcher
  unless r.counterExamples.isEmpty do
    throwError m!"missing cases:\n{counterExamplesToMessageData r.counterExamples}"
  unless r.unusedAltIdxs.isEmpty do
    throwError (m!"unused alternatives: " ++ toString (r.unusedAltIdxs.map fun idx => "#" ++ toString (idx+1)))
  let cinfo ← getConstInfo elimName
  IO.println (toString cinfo.name ++ " : " ++ toString cinfo.type)
  pure ()

def testFailure (ex : Name) (numPats : Nat) (elimName : Name) (inProp : Bool := false) : MetaM Unit := do
let worked ← tryCatch (do test ex numPats elimName inProp; pure true) (fun ex => pure false)
if worked then
  throwError "unexpected success"

def ex0 (x : Nat) : LHS (forall (y : Nat), Pat y)
:= default

#eval test `ex0 1 `elimTest0
#print elimTest0

def ex1 (α : Type u) (β : Type v) (n : Nat) (x : List α) (y : List β) :
  LHS (Pat ([] : List α) × Pat ([] : List β))
× LHS (forall (a : α) (as : List α) (b : β) (bs : List β), Pat (a::as) × Pat (b::bs))
× LHS (forall (a : α) (as : List α), Pat (a::as) × Pat ([] : List β))
× LHS (forall (b : β) (bs : List β), Pat ([] : List α) × Pat (b::bs))
:= default

#eval test `ex1 2 `elimTest1

#print elimTest1

inductive Vec (α : Type u) : Nat → Type u
| nil            : Vec α 0
| cons {n : Nat} : α → Vec α n → Vec α (n+1)

def ex2 (α : Type u) (n : Nat) (xs : Vec α n) (ys : Vec α n) :
  LHS (Pat (inaccessible 0) × Pat (Vec.nil : Vec α 0) × Pat (Vec.nil : Vec α 0))
× LHS (forall (n : Nat) (x : α) (xs : Vec α n) (y : α) (ys : Vec α n), Pat (inaccessible (n+1)) × Pat (Vec.cons x xs) × Pat (Vec.cons y ys)) :=
default

#eval test `ex2 3 `elimTest2
#print elimTest2

def ex3 (α : Type u) (β : Type v) (n : Nat) (x : List α) (y : List β) :
  LHS (Pat ([] : List α) × Pat ([] : List β))
× LHS (forall (a : α) (b : β), Pat [a] × Pat [b])
× LHS (forall (a₁ a₂ : α) (as : List α) (b₁ b₂ : β) (bs : List β), Pat (a₁::a₂::as) × Pat (b₁::b₂::bs))
× LHS (forall (as : List α) (bs : List β), Pat as × Pat bs)
:= default

-- set_option trace.Meta.EqnCompiler.match true
-- set_option trace.Meta.EqnCompiler.matchDebug true

#eval test `ex3 2 `elimTest3
#print elimTest3

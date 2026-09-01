/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean
public import Std.Data.HashMap.Basic

/-!
# Writer for the Lean 4 NDJSON export format

Serializes an `Environment`'s constants as newline-delimited JSON. See `doc/dev/export_format.md`
for the format itself.
-/

open Lean
open Std (HashMap)

def Lean.BinderInfo.toJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def Lean.ReducibilityHints.toJson : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular n => .mkObj [("regular", n.toNat)]

def Lean.QuotKind.toJson : QuotKind → Json
  | type => "type"
  | ctor => "ctor"
  | lift => "lift"
  | ind => "ind"

def Lean.DefinitionSafety.toJson : DefinitionSafety → Json
  | «unsafe» => "unsafe"
  | safe => "safe"
  | «partial» => "partial"

def Lean.KVMap.toJson (kvs: Lean.KVMap) : Json :=
  .mkObj <| kvs.entries.map (fun (k, v) => (k.toString, reprStr v))

namespace LeanExport

public structure Context where
  env : Environment

public structure State where
  visitedNames : HashMap Name Nat := HashMap.emptyWithCapacity 200000 |>.insert .anonymous 0
  visitedLevels : HashMap Level Nat := HashMap.emptyWithCapacity 1000 |>.insert .zero 0
  visitedExprs : HashMap Expr Nat := HashMap.emptyWithCapacity 10000000
  visitedConstants : NameHashSet := {}
  noMDataExprs : HashMap Expr Expr := HashMap.emptyWithCapacity 100000
  exportMData : Bool := false
  exportUnsafe : Bool := false
  ignoreMissing : Bool := false
  /-- Maps the name of an inductive type to a list of names of corresponding recursors.
  This is used to facilitate exporting of related inductives, constructors, and recursors as a unit. -/
  recursorMap : NameMap NameSet := {}

public abbrev M := ReaderT Context <| StateT State IO

public def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

/--
Initialize the exporter state from an environment and cli options.
The `recursorMap` maps each inductive declaration's name to the list
of relevant recursors, which is used to ensure that for any inductive
declaration, the inductives, constructors, and recursors are exported
together in that order.
-/
public def initState (env : Environment) (cliOptions : List String := []) : M Unit := do
  let mut recursorMap : NameMap NameSet := {}
  for (_, constInfo) in env.constants do
    if let .recInfo recVal := constInfo then
      for indName in recVal.all do
        recursorMap := recursorMap.alter indName <|
          fun
          | none => some <| NameSet.empty.insert recVal.name
          | some recNames => some <| recNames.insert recVal.name
  modify fun st => { st with
    exportMData   := cliOptions.any (· == "--export-mdata")
    exportUnsafe  := cliOptions.any (· == "--export-unsafe")
    ignoreMissing := cliOptions.any (· == "--ignore-missing")
    recursorMap
  }

/--
For a given primitive (name, level, expr) to be exported:
IFF it's been seen before, return its index within the export file
IFF it has not been seen before, add it to the cache, print it into the export, and return its cache index.
-/
@[inline]
def getIdx [Hashable α] [BEq α] (x : α) (namespaced: String) (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M Json) : M Nat := do
  let m ← getM <$> get
  if let some idx := m[x]? then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println (s.setObjVal! namespaced idx).compress
  modify fun st => setM st ((getM st).insert x idx)
  return idx

def dumpName (n : Name) : M Nat := getIdx n "in" (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => unreachable!
  | .str n s =>
    return .mkObj [
      ("str", .mkObj [
        ("pre", ← dumpName n),
        ("str", s)
      ])
    ]
  | .num n i =>
    return .mkObj [
      ("num", .mkObj [
        ("pre", ← dumpName n),
        ("i", i)
      ])
    ]

def dumpLevel (l : Level) : M Nat := getIdx l "il" (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero | .mvar _ => unreachable!
  | .succ l => return .mkObj [("succ", ← dumpLevel l)]
  | .max l1 l2 => return .mkObj [("max", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .imax l1 l2 => return .mkObj [("imax", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .param n => return .mkObj [("param", ← dumpName n)]

def dumpUparams (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  let _ ← (uparams.map (Level.param)).mapM dumpLevel
  pure nameIdxs.toJson

def dumpNames (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  return nameIdxs.toJson

def removeMData (e : Expr) : M Expr := do
  if let some x := (← get).noMDataExprs[e]? then
    return x
  let e' ← match e with
  | .mdata _ e' => removeMData e'
  | .fvar .. | .mvar ..=> unreachable!
  | .bvar .. | .sort .. | .const .. | .lit _ => pure e
  | .app f a =>
    pure <| e.updateApp! (← removeMData f) (← removeMData a)
  | .lam _ d b _ =>
    pure <| e.updateLambdaE! (← removeMData d) (← removeMData b)
  | .letE _ d v b _ =>
    -- Normalize `nonDep` to `false` to avoid duplicate expression indices.
    -- Lean's `BEq` for `Expr` considers the `nonDep` flag, but external type checkers
    -- (e.g., nanoda_lib) treat expressions as identical regardless of this optimization hint.
    -- Without normalization, the same expression can get different indices, causing parse errors.
    -- See: https://github.com/ammkrn/lean4export/commit/eb023e5
    pure <| e.updateLet! (← removeMData d) (← removeMData v) (← removeMData b) false
  | .forallE _ d b _ =>
    pure <| e.updateForallE! (← removeMData d) (← removeMData b)
  | .proj _ _ e2 =>
    pure <| e.updateProj! (← removeMData e2)
  modify (fun st => { st with noMDataExprs := st.noMDataExprs.insert e e' })
  pure e'

mutual

public partial def dumpExprAux (e : Expr) : M Nat := do
  getIdx e "ie" (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .fvar .. | .mvar .. => panic! "cannot export free variables or metavariables"
    | .mdata a e' =>
      return .mkObj [
        ("mdata", .mkObj [
            ("data", a.toJson),
            ("expr", ← dumpExprAux e')
        ])
      ]
    | .bvar i => return .mkObj [("bvar", i)]
    | .lit (.natVal i) => dumpNatDeps; return .mkObj [("natVal", s!"{i}")]
    | .lit (.strVal s) => dumpStrDeps; return .mkObj [("strVal", s)]
    | .sort l => return .mkObj [("sort", ← dumpLevel l)]
    | .const n us => return .mkObj [
      ("const", .mkObj [
        ("name", ← dumpName n),
        ("us", (← us.mapM dumpLevel).toJson)
      ])
    ]
    | .app f a => return .mkObj [
      ("app", .mkObj [
        ("fn", ← dumpExprAux f),
        ("arg", ← dumpExprAux a)
      ])
    ]
    | .lam n d b bi => return .mkObj [
      ("lam", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", bi.toJson)
      ])
    ]
    | .forallE n d b bi => return .mkObj [
      ("forallE", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", bi.toJson)
      ])
    ]
    | .letE n d v b nondep => return .mkObj [
      ("letE", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("value", ← dumpExprAux v),
        ("body", ← dumpExprAux b),
        ("nondep", nondep)
      ])
    ]
    | .proj s i e => return .mkObj [
      ("proj", .mkObj [
        ("typeName", ← dumpName s),
        ("idx", i),
        ("struct", ← dumpExprAux e)
      ])
    ]
where
  dumpNatDeps : M Unit := do
    let nat := ``Nat
    if (!(← get).visitedConstants.contains nat) && ((← read).env.find? nat).isSome
    then dumpConstant nat
  dumpStrDeps : M Unit := do
    let charOfNat := ``Char.ofNat
    if (!(← get).visitedConstants.contains charOfNat) && ((← read).env.find? charOfNat).isSome
    then dumpConstant charOfNat
    let stringOfList := ``String.ofList
    if (!(← get).visitedConstants.contains stringOfList) && ((← read).env.find? stringOfList).isSome
    then dumpConstant stringOfList

public partial def dumpExpr (e : Expr) : M Nat := do
    let aux (e : Expr) : M Expr := do
      modify (fun st => { st with noMDataExprs := HashMap.emptyWithCapacity })
      removeMData e
    dumpExprAux <| ← if (← get).exportMData then pure e else aux e

public partial def dumpConstant (c : Name) : M Unit := do
  let some declar := (← read).env.find? c
    | if (← get).ignoreMissing then return else panic! s!"Constant {c} not found in environment."
  if (declar.isUnsafe && !(← get).exportUnsafe) || (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match declar with
  | .axiomInfo val => do
    dumpDeps val.type
    dumpObj [
      ("axiom", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .defnInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("def", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("hints", val.hints.toJson),
        ("safety", val.safety.toJson),
        ("all", ← dumpNames val.all)
      ])
    ]
  | .opaqueInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("opaque", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("thm", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all)
      ])
    ]
  | .quotInfo _ =>
    -- Always dump full Quot package in the sensible order
    dumpConstant ``Eq
    for c in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let some (.quotInfo val) := (← read).env.find? c
        | if (← get).ignoreMissing then return else panic! s!"Constant {c} not found in environment."
      modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
      dumpObj [
        ("quot", .mkObj [
          ("name", ← dumpName val.name),
          ("levelParams", ← dumpUparams val.levelParams),
          ("type", ← dumpExpr val.type),
          ("kind", val.kind.toJson)
        ])
      ]
  | .inductInfo baseIndVal => do
    let mut indVals := #[]
    let mut ctorVals := #[]
    let mut recursorNames := NameSet.empty
    for indName in baseIndVal.all do
      let val := ((← read).env.find? indName |>.get!).inductiveVal!
      assert! ((!val.isUnsafe) || (← get).exportUnsafe)
      indVals := indVals.push val
      for ctor in val.ctors do
        match ((← read).env.find? ctor |>.get!) with
        | .ctorInfo ctorVal =>
          assert! ((!ctorVal.isUnsafe) || (← get).exportUnsafe)
          ctorVals := ctorVals.push ctorVal
        | _ => panic! "Expected a `ConstantInfo.ctorInfo`."
      modify fun st => { st with visitedConstants:= st.visitedConstants.insert indName }
      dumpDeps val.type
      if let .some names := (← get).recursorMap.get? baseIndVal.name
      then recursorNames := recursorNames.union names
      else assert! ctorVals.size == 0

    /- We dump the constructor dependencies (which will not include the inductives in this block since we've
    added the names to `visitedConstants`) before actually outputting anything in this inductive block to
    ensure e.g. the `LT` in `Fin.mk` is dumped before this inductive block appears in the export file. -/
    for ctorVal in ctorVals do
      modify fun st => { st with visitedConstants:= st.visitedConstants.insert ctorVal.name }
      dumpDeps ctorVal.type

    let mut recursorVals := #[]
    for recursorName in recursorNames do
      match ((← read).env.find? recursorName |>.get!) with
      | .recInfo recVal =>
        assert! ((!recVal.isUnsafe) || (← get).exportUnsafe)
        recursorVals := recursorVals.push recVal
      | _ => panic! "expected a `constantinfo.recinfo`."
    for recursorVal in recursorVals do
      modify fun st => { st with visitedConstants:= st.visitedConstants.insert recursorVal.name }
      dumpDeps recursorVal.type

    /- We only dump these after we've already dumped the `recursorVal` type and added the name
    to `visitedConstants` so that `dumpDeps` does not retry dumping the appearance of `Foo.rec` -/
    for recursorVal in recursorVals do
      for rule in recursorVal.rules do
        dumpDeps rule.rhs

    let inductiveValsJson ← indVals.mapM <| fun indVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName indVal.name),
          ("levelParams", ← dumpUparams indVal.levelParams),
          ("type", ← dumpExpr indVal.type),
          ("numParams", indVal.numParams),
          ("numIndices", indVal.numIndices),
          ("all", ← dumpNames indVal.all),
          ("ctors", ← dumpNames indVal.ctors),
          ("numNested", indVal.numNested),
          ("isRec", indVal.isRec),
          ("isReflexive", indVal.isReflexive),
          ("isUnsafe", indVal.isUnsafe),
      ]
    let ctorValsJson ← ctorVals.mapM <| fun ctorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName ctorVal.name),
          ("levelParams", ← dumpUparams ctorVal.levelParams),
          ("type", ← dumpExpr ctorVal.type),
          ("induct", ← dumpName ctorVal.induct),
          ("cidx", ctorVal.cidx),
          ("numParams", ctorVal.numParams),
          ("numFields", ctorVal.numFields),
          ("isUnsafe", ctorVal.isUnsafe)
      ]
    let recursorValsJson ← recursorVals.mapM <| fun recursorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName recursorVal.name),
          ("levelParams", ← dumpUparams recursorVal.levelParams),
          ("type", ← dumpExpr recursorVal.type),
          ("all", ← dumpNames recursorVal.all),
          ("numParams", recursorVal.numParams),
          ("numIndices", recursorVal.numIndices),
          ("numMotives", recursorVal.numMotives),
          ("numMinors", recursorVal.numMinors),
          ("rules", (← recursorVal.rules.mapM dumpRecRule).toJson),
          ("k", recursorVal.k),
          ("isUnsafe", recursorVal.isUnsafe),
      ]
    dumpObj [
      ("inductive", Json.mkObj [
        ("types", inductiveValsJson.toJson),
        ("ctors", ctorValsJson.toJson),
        ("recs", recursorValsJson.toJson),
      ])
    ]
  | .ctorInfo val => dumpConstant val.induct
  | .recInfo val =>
    for indName in val.all do
      dumpConstant indName
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
  /- Return these for inclusion inline with the exported `recInfo`. -/
  dumpRecRule (rule : RecursorRule) : M Json := do
    return Json.mkObj [
      ("ctor", ← dumpName rule.ctor),
      ("nfields", rule.nfields),
      ("rhs", ← dumpExpr rule.rhs),
    ]
  dumpObj (fields : List (String × Json)) : M Unit :=
    IO.println <| Json.mkObj fields |>.compress

end

def exportMetadata : Json :=
  let leanMeta := Json.mkObj [
    ("version", versionString),
    ("githash", githash)
  ]
  let exporterMeta := Json.mkObj [
    ("name", "lean4export"),
    ("version", "3.1.0")
  ]
  let formatMeta := Json.mkObj [
    ("version", "3.1.0")
  ]

  Json.mkObj [
    ("meta", Json.mkObj [
      ("exporter", exporterMeta),
      ("lean", leanMeta),
      ("format", formatMeta)
    ])
  ]

public def dumpMetadata : M Unit := do
  IO.println exportMetadata.compress

end LeanExport

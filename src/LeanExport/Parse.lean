/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Data.HashMap
public import Lean.Declaration
import Init.Data.Array.GetLit
import Init.Data.String.Search
import Init.System.IO
import Std.Internal.Parsec.String
import Lean.Data.Json.Parser

/-!
# Reader for the Lean 4 NDJSON export format

Reconstructs a constant map from an export produced by `LeanExport.Basic`. The result is a plain
`Std.HashMap`, not an `Environment`: nothing here is trusted, and nothing is added to the
environment of the process doing the reading.
-/

namespace LeanExport

public structure ExportedEnv where
  constMap : Std.HashMap Lean.Name Lean.ConstantInfo
  constOrder : Array Lean.Name
  deriving Inhabited

namespace Parse


open Std.Internal.Parsec Std.Internal.Parsec.String Lean

structure State where
  stream : IO.FS.Stream
  nameMap : Std.HashMap Nat Lean.Name := { (0, .anonymous) }
  levelMap : Std.HashMap Nat Lean.Level := { (0, .zero) }
  exprMap : Std.HashMap Nat Lean.Expr := {}
  recursorRuleMap : Std.HashMap Nat Lean.RecursorRule := {}
  constMap : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  constOrder : Array Lean.Name := #[]

abbrev M := StateT State <| IO

def M.run (x : M α) (stream : IO.FS.Stream) : IO (α × State) := do
  StateT.run x { stream := stream }

@[inline]
def fail (msg : String) : M α :=
  throw (.userError msg)

@[inline]
def getName (nidx : Nat) : M Lean.Name := do
  let some n := (← get).nameMap[nidx]? | fail s!"Name not found {nidx}"
  return n

@[inline]
def addName (nidx : Nat) (n : Lean.Name) : M Unit := do
  modify fun s => { s with nameMap := s.nameMap.insert nidx n }

@[inline]
def getLevel (uidx : Nat) : M Lean.Level := do
  let some l := (← get).levelMap[uidx]? | fail s!"Level not found {uidx}"
  return l

@[inline]
def addLevel (uidx : Nat) (l : Lean.Level) : M Unit := do
  modify fun s => { s with levelMap := s.levelMap.insert uidx l }

@[inline]
def getExpr (eidx : Nat) : M Lean.Expr := do
  let some e := (← get).exprMap[eidx]? | fail s!"Expr not found {eidx}"
  return e

@[inline]
def addExpr (eidx : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }

@[inline]
def getRecursorRule (ridx : Nat) : M Lean.RecursorRule := do
  let some r := (← get).recursorRuleMap[ridx]? | fail s!"RecursorRule not found {ridx}"
  return r

@[inline]
def addRecursorRule (ridx : Nat) (r : Lean.RecursorRule) : M Unit := do
  modify fun s => { s with recursorRuleMap := s.recursorRuleMap.insert ridx r }

@[inline]
def addConst (name : Lean.Name) (d : Lean.ConstantInfo) : M Unit := do
  if (← get).constMap.contains name then
    fail s!"Duplicate declaration: {name}"
  modify fun s => {
    s with
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
    }

@[inline]
def parseJsonObj (line : String) : M (Std.TreeMap.Raw String Json) := do
  let .ok (.obj obj) := Json.Parser.anyCore.run line | fail "Expected JSON object"
  return obj

def parseNameStr (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.str invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.str str) := data["str"]? | fail s!"Name.str invalid"
  return .str (← getName preIdx) str

def parseNameNum (json : Json) : M Name := do
  let .obj data := json | fail s!"Name.num invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str invalid"
  let some (.num (i : Nat)) := data["i"]? | fail s!"Name.num invalid"
  return .num (← getName preIdx) i

def parseLevelSucc (json : Json) : M Level := do
  let .num (lIdx : Nat) := json | fail s!"Level.succ invalid"
  return .succ (← getLevel lIdx)

def parseLevelMax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.max invalid"
  return .max (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelImax (json : Json) : M Level := do
  let .arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)] := json
    | fail s!"Level.imax invalid"
  return .imax (← getLevel lhsIdx) (← getLevel rhsIdx)

def parseLevelParam (json : Json) : M Level := do
  let .num (nIdx : Nat) := json | fail s!"Level.param invalid"
  return .param (← getName nIdx)

def parseExprBVar (json : Json) : M Expr := do
  let .num (deBruijnIndex : Nat) := json | fail s!"Expr.bvar invalid"
  return .bvar deBruijnIndex

def parseExprSort (json : Json) : M Expr := do
  let .num (uIdx : Nat) := json | fail s!"Expr.sort invalid"
  return .sort (← getLevel uIdx)

def parseExprConst (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.const invalid"
  let some (.num (declNameIdx : Nat)) := data["name"]? | fail s!"Expr.const invalid"
  let some (.arr usIdxs) := data["us"]? | fail s!"Expr.const invalid"

  let declName ← getName declNameIdx
  let us ← usIdxs.mapM fun uIdx => do
    let (.num (uIdx : Nat)) := uIdx | fail s!"Expr.const invalid"
    getLevel uIdx

  return .const declName us.toList

def parseExprApp (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.app invalid"
  let some (.num (fnIdx : Nat)) := data["fn"]? | fail s!"Expr.app invalid"
  let some (.num (argIdx : Nat)) := data["arg"]? | fail s!"Expr.app invalid"
  let fn ← getExpr fnIdx
  let arg ← getExpr argIdx

  return .app fn arg

def parseBinderInfo (info : String) : M BinderInfo :=
  match info with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => fail s!"Invalid binder info: {info}"

def parseExprLam (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.lam invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.lam invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.lam invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.lam invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.lam invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr

  return .lam binderName binderType body binderInfo

def parseExprForallE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.forallE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.forallE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.forallE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.forallE invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.forallE invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr

  return .forallE binderName binderType body binderInfo

def parseExprLetE (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.letE invalid"
  let some (.num (binderNameIdx : Nat)) := data["name"]? | fail s!"Expr.letE invalid"
  let some (.num (binderTypeIdx : Nat)) := data["type"]? | fail s!"Expr.letE invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"Expr.letE invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.letE invalid"
  let some (.bool nondep) := data["nondep"]? | fail s!"Expr.letE invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let value ← getExpr valueIdx
  let body ← getExpr bodyIdx

  return .letE binderName binderType value body nondep

def parseExprProj (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.proj invalid"
  let some (.num (typeNameIdx : Nat)) := data["typeName"]? | fail s!"Expr.proj invalid"
  let some (.num (projIdx : Nat)) := data["idx"]? | fail s!"Expr.proj invalid"
  let some (.num (structIdx : Nat)) := data["struct"]? | fail s!"Expr.proj invalid"

  let typeName ← getName typeNameIdx
  let struct ← getExpr structIdx

  return .proj typeName projIdx struct

def parseExprNatLit (json : Json) : M Expr := do
  let .str natValStr := json | fail s!"Expr.lit natVal invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal invalid"

  return .lit (.natVal natVal)

def parseExprStrLit (json : Json) : M Expr := do
  let .str strVal := json | fail s!"Expr.lit strVal invalid"
  return .lit (.strVal strVal)

def parseExprMdata (json : Json) : M Expr := do
  let .obj data := json | fail s!"Expr.mdata invalid"
  let some (.num (exprIdx : Nat)) := data["expr"]? | fail s!"Expr.mdata invalid"
  let some (.obj _dataObj) := data["data"]? | fail s!"Expr.mdata invalid"
  let expr ← getExpr exprIdx

  -- TODO: Unclear how to perfectly recover with the current output format
  return .mdata {} expr

def getNameList (idxs : Array Json) : M (List Name) := do
  idxs.toList.mapM fun idx => do
    let (.num (idx : Nat)) := idx | fail s!"failed to convert to name idx"
    getName idx

def parseAxiomInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"axiomInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"axiomInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"axiomInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"axiomInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx

  addConst name <| .axiomInfo { name, levelParams, type, isUnsafe }

def parseDefnInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"defnInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"defnInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"defnInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"defnInfo invalid"
  let some hints := data["hints"]? | fail s!"defnInfo invalid"
  let some (.str safetyStr) := data["safety"]? | fail s!"defnInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"defnInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let hints ←
    match hints with
    | .str "opaque" => pure .opaque
    | .str "abbrev" => pure .abbrev
    | .obj obj =>
      let some (.num (level : Nat)) := obj["regular"]? | fail s!"defnInfo invalid"
      pure <| .regular level.toUInt32
    | _ => fail s!"defnInfo invalid"
  let safety ←
    match safetyStr with
    | "unsafe" => pure .unsafe
    | "safe" => pure .safe
    | "partial" => pure .partial
    | _ => fail s!"Unknown safety parameter: {safetyStr}"
  let all ← getNameList allIdxs

  addConst name <| .defnInfo { name, levelParams, type, value, hints, safety, all }

def parseThmInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"thmInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"thmInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"thmInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"thmInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"thmInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs

  addConst name <| .thmInfo { name, levelParams, type, value, all }

def parseOpaqueInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"opaqueInfo invalid"
  -- Work around until the exporter always includes isUnsafe
  let (.bool isUnsafe) := data["isUnsafe"]?.getD (.bool false) | fail s!"axiomInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"opaqueInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs

  addConst name <| .opaqueInfo { name, levelParams, type, value, all, isUnsafe }

def parseQuotInfo (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"quotInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"quotInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"quotInfo invalid"
  let some (.str kindStr) := data["kind"]? | fail s!"quotInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let kind ←
    match kindStr with
    | "type" => pure .type
    | "ctor" => pure .ctor
    | "lift" => pure .lift
    | "ind" => pure .ind
    | _ => fail s!"unknown quot kind: {kindStr}"

  addConst name <| .quotInfo { name, levelParams, type, kind }

def parseInductInfo (json : Json) : M Unit := do
  let .obj data := json | fail "inductInfo invalid: Expected JSON object"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"inductInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"inductInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"inductInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"inductInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"inductInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"inductInfo invalid"
  let some (.arr ctorsIdxs) := data["ctors"]? | fail s!"inductInfo invalid"
  let some (.num (numNested : Nat)) := data["numNested"]? | fail s!"inductInfo invalid"
  let some (.bool isRec) := data["isRec"]? | fail s!"inductInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"inductInfo invalid"
  let some (.bool isReflexive) := data["isReflexive"]? | fail s!"inductInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let ctors ← getNameList ctorsIdxs

  addConst name <| .inductInfo {
    name,
    levelParams,
    type,
    numParams,
    numIndices,
    all,
    ctors,
    numNested,
    isRec,
    isUnsafe,
    isReflexive,
  }

def parseCtorInfo (json : Json) : M Unit := do
  let .obj data := json | fail s!"ctorInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"ctorInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"ctorInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"ctorInfo invalid"
  let some (.num (inductIdx : Nat)) := data["induct"]? | fail s!"ctorInfo invalid"
  let some (.num (cidx : Nat)) := data["cidx"]? | fail s!"ctorInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"ctorInfo invalid"
  let some (.num (numFields : Nat)) := data["numFields"]? | fail s!"ctorInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"ctorInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let induct ← getName inductIdx

  addConst name <| .ctorInfo {
    name,
    levelParams,
    type,
    induct,
    cidx,
    numParams,
    numFields,
    isUnsafe,
  }

def parseRecInfo (json : Json) : M Unit := do
  let .obj data := json | fail s!"recInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"recInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"recInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"recInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"recInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"recInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"recInfo invalid"
  let some (.num (numMotives : Nat)) := data["numMotives"]? | fail s!"recInfo invalid"
  let some (.num (numMinors : Nat)) := data["numMinors"]? | fail s!"recInfo invalid"
  let some (.bool k) := data["k"]? | fail s!"recInfo invalid"
  let some (.arr rules) := data["rules"]? | fail s!"recInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"recInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let rules ← rules.toList.mapM fun rule => do
    let .obj rule := rule | fail s!"recInfo invalid"
    let some (.num (ctorIdx : Nat)) := rule["ctor"]? | fail s!"recInfo invalid"
    let some (.num (nfields : Nat)) := rule["nfields"]? | fail s!"recInfo invalid"
    let some (.num (rhsIdx : Nat)) := rule["rhs"]? | fail s!"recInfo invalid"

    let ctor ← getName ctorIdx
    let rhs ← getExpr rhsIdx
    return { ctor, nfields, rhs }

  addConst name <| .recInfo {
    name,
    levelParams,
    type,
    all,
    numParams,
    numIndices,
    numMotives,
    numMinors,
    rules,
    k,
    isUnsafe,
  }

def parseInductive (data : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.arr types) := data["types"]? | fail s!"Inductive invalid, no `types`"
  let some (.arr ctors) := data["ctors"]? | fail s!"Inductive invalid, no `ctors`"
  let some (.arr recs) := data["recs"]? | fail s!"Inductive invalid, no `recs`"
  types.forM parseInductInfo
  ctors.forM parseCtorInfo
  recs.forM parseRecInfo

def parseItem (line : String) : M Unit := do
  let obj ← parseJsonObj line
  let kv := obj.toList
  -- Normalize key order...
  let kv := match kv with
    | [x, y@("in", _)] => [y,x]
    | [x, y@("ie", _)] => [y,x]
    | [x, y@("il", _)] => [y,x]
    | _ =>kv
  -- so that we can match on it easily
  match kv with
  | [("in", .num (idx : Nat)),("str", data)] =>   addName idx <| ← parseNameStr data
  | [("in", .num (idx : Nat)),("num", data)] =>   addName idx <| ← parseNameNum data
  | [("il", .num (idx : Nat)),("succ", data)] =>  addLevel idx <| ← parseLevelSucc data
  | [("il", .num (idx : Nat)),("max", data)] =>   addLevel idx <| ← parseLevelMax data
  | [("il", .num (idx : Nat)),("imax", data)] =>  addLevel idx <| ← parseLevelImax data
  | [("il", .num (idx : Nat)),("param", data)] => addLevel idx <| ← parseLevelParam data
  | [("ie", .num (idx : Nat)),("bvar", data)] =>  addExpr idx <| ← parseExprBVar data
  | [("ie", .num (idx : Nat)),("sort", data)] =>  addExpr idx <| ← parseExprSort data
  | [("ie", .num (idx : Nat)),("const", data)] => addExpr idx <| ← parseExprConst data
  | [("ie", .num (idx : Nat)),("app", data)] =>   addExpr idx <| ← parseExprApp data
  | [("ie", .num (idx : Nat)),("lam", data)] =>   addExpr idx <| ← parseExprLam data
  | [("ie", .num (idx : Nat)),("forallE", data)] =>addExpr idx <| ← parseExprForallE data
  | [("ie", .num (idx : Nat)),("letE", data)] =>   addExpr idx <| ← parseExprLetE data
  | [("ie", .num (idx : Nat)),("proj", data)] =>   addExpr idx <| ← parseExprProj data
  | [("ie", .num (idx : Nat)),("natVal", data)] => addExpr idx <| ← parseExprNatLit data
  | [("ie", .num (idx : Nat)),("strVal", data)] => addExpr idx <| ← parseExprStrLit data
  | [("ie", .num (idx : Nat)),("mdata", data)] => addExpr idx <| ← parseExprMdata data
  | [("axiom", .obj data)] => parseAxiomInfo data
  | [("def", .obj data)] => parseDefnInfo data
  | [("thm", .obj data)] => parseThmInfo data
  | [("opaque", .obj data)] => parseOpaqueInfo data
  | [("quot", .obj data)] => parseQuotInfo data
  | [("inductive", .obj data)] => parseInductive data
  | _ => fail s!"Unknown export object with keys {obj.keys}"

partial def parseItems : M Unit :=
  go
where
  go : M Unit := do
    let line ← (← get).stream.getLine
    unless line.isEmpty do
      parseItem line
      go

def parseMdata : M Unit := do
  let _line ← (← get).stream.getLine

def parseFile : M Unit := do
  parseMdata
  parseItems

end Parse

public def parseStream (stream : IO.FS.Stream) : IO ExportedEnv := do
  let (_, state) ← Parse.M.run Parse.parseFile stream
  let { constMap, constOrder, .. } := state
  return {
    constMap,
    constOrder,
  }

-- We cannot turn pure Strings into Streams?
-- def parse (input : String) : Except String ExportedEnv := do
--   parseStream (IO.FS.Stream.ofString input)


end LeanExport

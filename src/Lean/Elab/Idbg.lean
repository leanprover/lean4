/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Std.Async.TCP

/-!
# Interactive Debug Expression Evaluator (`idbg`)

`idbg` enables live communication between a running compiled Lean program and the language server.

## Protocol

Communication uses a length-prefixed TCP protocol over localhost. Both server (language server side)
and client (compiled program side) compute a deterministic port from the source location hash.
-/

open Lean Lean.Elab Lean.Elab.Term Lean.Meta
open Std.Net Std.Async

namespace Lean.Idbg

/-- Custom `Name` serialization that preserves the exact structure.
The standard `ToJson`/`FromJson Name` uses `toString`/`toName` which doesn't
round-trip for hygienic names (e.g., names containing `@`). -/
def nameToJson : Name → Json
  | .anonymous => Json.null
  | .str p s   => Json.mkObj [("str", Json.arr #[nameToJson p, toJson s])]
  | .num p n   => Json.mkObj [("num", Json.arr #[nameToJson p, n])]

/-- Inverse of `nameToJson`. -/
partial def nameFromJson? (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  if let some arr := (j.getObjVal? "str").toOption then
    let #[p, s] := (← fromJson? arr : Array Json) | .error "str expects 2 elements"
    return .str (← nameFromJson? p) (← fromJson? s)
  if let some arr := (j.getObjVal? "num").toOption then
    let #[p, n] := (← fromJson? arr : Array Json) | .error "num expects 2 elements"
    return .num (← nameFromJson? p) (← fromJson? n)
  .error s!"expected Name, got {j}"

/-- Serialize `BinderInfo` to JSON. -/
def binderInfoToJson : BinderInfo → Json
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

/-- Deserialize `BinderInfo` from JSON. -/
def binderInfoFromJson? : Json → Except String BinderInfo
  | .str "default"        => .ok .default
  | .str "implicit"       => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit"   => .ok .instImplicit
  | j => .error s!"expected BinderInfo, got {j}"

/-- Serialize `Literal` to JSON. -/
def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("natVal", n)]
  | .strVal s => Json.mkObj [("strVal", s)]

/-- Deserialize `Literal` from JSON. -/
def literalFromJson? (j : Json) : Except String Literal := do
  if let some n := (j.getObjVal? "natVal").toOption then
    return .natVal (← fromJson? n)
  if let some s := (j.getObjVal? "strVal").toOption then
    return .strVal (← fromJson? s)
  .error s!"expected Literal, got {j}"

/-- Serialize `Level` to JSON. -/
partial def levelToJson : Level → Json
  | .zero     => Json.mkObj [("zero", Json.null)]
  | .succ l   => Json.mkObj [("succ", levelToJson l)]
  | .max a b  => Json.mkObj [("max", Json.arr #[levelToJson a, levelToJson b])]
  | .imax a b => Json.mkObj [("imax", Json.arr #[levelToJson a, levelToJson b])]
  | .param n  => Json.mkObj [("param", nameToJson n)]
  | .mvar id  => Json.mkObj [("mvar", nameToJson id.name)]

/-- Deserialize `Level` from JSON. -/
partial def levelFromJson? (j : Json) : Except String Level := do
  if (j.getObjVal? "zero").toOption.isSome then
    return .zero
  if let some l := (j.getObjVal? "succ").toOption then
    return .succ (← levelFromJson? l)
  if let some arr := (j.getObjVal? "max").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "max expects 2 elements"
    return .max (← levelFromJson? a) (← levelFromJson? b)
  if let some arr := (j.getObjVal? "imax").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "imax expects 2 elements"
    return .imax (← levelFromJson? a) (← levelFromJson? b)
  if let some n := (j.getObjVal? "param").toOption then
    return .param (← nameFromJson? n)
  if let some n := (j.getObjVal? "mvar").toOption then
    return .mvar ⟨← nameFromJson? n⟩
  .error s!"expected Level, got {j}"

/-- Serialize `Expr` to JSON. Metadata is stripped; free variables are preserved. -/
partial def exprToJson : Expr → Json
  | .bvar i          => Json.mkObj [("bvar", i)]
  | .fvar id         => Json.mkObj [("fvar", nameToJson id.name)]
  | .mvar id         => Json.mkObj [("mvar", nameToJson id.name)]
  | .sort l          => Json.mkObj [("sort", levelToJson l)]
  | .const n ls      => Json.mkObj [("const", nameToJson n), ("levels", Json.arr (ls.toArray.map levelToJson))]
  | .app fn arg      => Json.mkObj [("app", Json.arr #[exprToJson fn, exprToJson arg])]
  | .lam n ty b bi   => Json.mkObj [("lam", Json.mkObj [("name", nameToJson n), ("type", exprToJson ty), ("body", exprToJson b), ("bi", binderInfoToJson bi)])]
  | .forallE n ty b bi => Json.mkObj [("forallE", Json.mkObj [("name", nameToJson n), ("type", exprToJson ty), ("body", exprToJson b), ("bi", binderInfoToJson bi)])]
  | .letE n ty v b nd => Json.mkObj [("letE", Json.mkObj [("name", nameToJson n), ("type", exprToJson ty), ("value", exprToJson v), ("body", exprToJson b), ("nondep", nd)])]
  | .lit l           => Json.mkObj [("lit", literalToJson l)]
  | .mdata _ e       => exprToJson e  -- strip metadata
  | .proj tn i s     => Json.mkObj [("proj", Json.mkObj [("typeName", nameToJson tn), ("idx", i), ("struct", exprToJson s)])]

/-- Deserialize `Expr` from JSON. -/
partial def exprFromJson? (j : Json) : Except String Expr := do
  if let some i := (j.getObjVal? "bvar").toOption then
    return .bvar (← fromJson? i)
  if let some id := (j.getObjVal? "fvar").toOption then
    return .fvar ⟨← nameFromJson? id⟩
  if let some id := (j.getObjVal? "mvar").toOption then
    return .mvar ⟨← nameFromJson? id⟩
  if let some l := (j.getObjVal? "sort").toOption then
    return .sort (← levelFromJson? l)
  if (j.getObjVal? "const").toOption.isSome then
    let n ← nameFromJson? (← j.getObjVal? "const")
    let ls : Array Json ← fromJson? (← j.getObjVal? "levels")
    return .const n (← ls.toList.mapM levelFromJson?)
  if let some arr := (j.getObjVal? "app").toOption then
    let #[fn, arg] := (← fromJson? arr : Array Json) | .error "app expects 2 elements"
    return .app (← exprFromJson? fn) (← exprFromJson? arg)
  if let some obj := (j.getObjVal? "lam").toOption then
    return .lam (← nameFromJson? (← obj.getObjVal? "name"))
      (← exprFromJson? (← obj.getObjVal? "type"))
      (← exprFromJson? (← obj.getObjVal? "body"))
      (← binderInfoFromJson? (← obj.getObjVal? "bi"))
  if let some obj := (j.getObjVal? "forallE").toOption then
    return .forallE (← nameFromJson? (← obj.getObjVal? "name"))
      (← exprFromJson? (← obj.getObjVal? "type"))
      (← exprFromJson? (← obj.getObjVal? "body"))
      (← binderInfoFromJson? (← obj.getObjVal? "bi"))
  if let some obj := (j.getObjVal? "letE").toOption then
    return .letE (← nameFromJson? (← obj.getObjVal? "name"))
      (← exprFromJson? (← obj.getObjVal? "type"))
      (← exprFromJson? (← obj.getObjVal? "value"))
      (← exprFromJson? (← obj.getObjVal? "body"))
      (← fromJson? (← obj.getObjVal? "nondep"))
  if let some l := (j.getObjVal? "lit").toOption then
    return .lit (← literalFromJson? l)
  if let some obj := (j.getObjVal? "proj").toOption then
    return .proj (← nameFromJson? (← obj.getObjVal? "typeName"))
      (← fromJson? (← obj.getObjVal? "idx"))
      (← exprFromJson? (← obj.getObjVal? "struct"))
  .error s!"expected Expr, got {j}"

/-- Deterministic port for a given `idbg` site, in range [10000, 65535]. -/
def idbgPort (siteId : String) : UInt16 :=
  let h := hash siteId
  (h % 55535 + 10000).toUInt16

def sendMsg (client : TCP.Socket.Client) (msg : String) : IO Unit := do
  let bytes := msg.toUTF8
  let header := s!"{bytes.size}\n".toUTF8
  let t ← (client.sendAll #[header, bytes]).toIO
  t.block

def recvMsg (client : TCP.Socket.Client) : IO String := do
  -- Read until newline to get the decimal length
  let mut header := ByteArray.empty
  repeat
    let t ← (client.recv? 1).toIO
    let some chunk ← t.block | throw (.userError "idbg: connection closed")
    if chunk[0]! == '\n'.toUInt8 then break
    header := header ++ chunk
  let some lenStr := String.fromUTF8? header | throw (.userError "idbg: invalid header")
  let some len := lenStr.toNat? | throw (.userError "idbg: invalid length")
  let mut payload := ByteArray.empty
  while payload.size < len do
    let t ← (client.recv? (len - payload.size).toUInt64).toIO
    let some chunk ← t.block | throw (.userError "idbg: connection closed")
    payload := payload ++ chunk
  let some s := String.fromUTF8? payload | throw (.userError "idbg: invalid UTF-8")
  return s

/-- Start a TCP server on the deterministic port for this site,
wait for one connection, send expression JSON, and receive the result string.
Returns `none` if the port is still held by a previous (cancelled) server. -/
def idbgServer (siteId : String) (exprJson : Json) : IO (Option String) := do
  let port := idbgPort siteId
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port
  let mut server? : Option TCP.Socket.Server := none
  for _ in List.range 100 do  -- retry for up to 10s
    match (← (do let s ← TCP.Socket.Server.mk; s.bind addr; s.listen 1; return s).toBaseIO) with
    | .ok s => server? := some s; break
    | .error _ => IO.sleep 100
  let some server := server? | return none
  let t ← server.accept |>.toIO
  let client ← t.block
  sendMsg client exprJson.compress
  let result ← recvMsg client
  let t ← client.shutdown |>.toIO
  t.block
  return some result

/-- Load the program's environment from its imports.
The imports include the current module (appended last by the elaborator) so that
same-file declarations are available. If its `.olean` is not found (e.g., when
running `lean` directly), we fall back to just the transitive imports. -/
def idbgLoadEnv (imports : Array Import) : IO Environment := do
  try
    importModules imports {} 0
  catch _ =>
    importModules imports.pop {} 0

/-- Compile and evaluate an expression in the given environment. -/
def idbgCompileAndEval (α : Type) [Nonempty α]
    (env : Environment) (type value : Expr) : IO α := do
  let name := `_idbg
  let decl := Declaration.defnDecl {
    name
    levelParams := []
    type
    value
    hints := .opaque
    safety := .unsafe
  }
  let ((), {env := env', ..}) ← (addAndCompile decl).toIO
    { fileName := "<idbg>", fileMap := default, options := {} }
    { env }
  match unsafe env'.evalConst α {} name (checkMeta := false) with
  | .ok val => return val
  | .error msg => throw (.userError s!"idbg evalConst failed: {msg}")

/-- Connect to the debug server, receive expressions, evaluate, send results. Loops forever. -/
@[nospecialize, export lean_idbg_client_loop] def idbgClientLoopImpl
    (siteId : String) (imports : Array Import) (apply : NonScalar → String) : IO Unit := do
  let baseEnv ← idbgLoadEnv imports
  let port := idbgPort siteId
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port
  while true do
    try
      let client ← TCP.Socket.Client.mk
      let t ← (client.connect addr).toIO
      t.block
      let msg ← recvMsg client
      let json ← IO.ofExcept (Json.parse msg)
      let type ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "type")))
      let value ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "value")))
      let fnVal ← idbgCompileAndEval NonScalar baseEnv type value
      let result := apply fnVal
      sendMsg client result
      let t ← client.shutdown |>.toIO
      t.block
    catch e =>
      -- Only log non-connection errors (connection refused is normal during reconnect)
      let msg := toString e
      unless (msg.find? "connection refused").isSome do
        IO.eprintln s!"idbg client: {e}"
      IO.sleep 500

end Lean.Idbg

namespace Lean.Elab.Do

open Lean.Idbg

@[builtin_doElem_control_info Lean.Parser.Term.doIdbg]
def controlInfoIdbg : ControlInfoHandler := fun _ => return default

/-- Core elaboration logic shared by term and do-element forms.
Elaborates `e`, wraps the result in `toString ∘ repr`, abstracts over all local declarations,
and generates both the server-side TCP exchange and the runtime client loop code. -/
private def elabIdbgCore (e : Syntax) (body : TSyntax `term) (ref : Syntax) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let fileName ← IO.FS.realPath (← getFileName)
  let siteId := toString (hash s!"{fileName}:{ref.getPos?.getD 0}")

  -- Collect ALL non-aux local declarations.
  -- We need all of them (not just those used in the current expression)
  -- because the expression can change on the server side while the
  -- compiled program's apply closure is fixed.
  let lctx ← getLCtx
  let mut localDecls : Array LocalDecl := #[]
  for decl in lctx do
    if decl.isAuxDecl then continue
    localDecls := localDecls.push decl
  let localFVars := localDecls.map (mkFVar ·.fvarId)

  -- Elaborate e, wrap in `toString ∘ repr`.
  -- `synthesizeSyntheticMVarsNoPostponing` forces pending instance resolution
  -- so that `instantiateMVars` can fully resolve all metavariables.
  let eExpr ← Term.elabTerm e none
  Term.synthesizeSyntheticMVarsNoPostponing
  let eExpr ← instantiateMVars eExpr
  let reprExpr ← Meta.mkAppM ``repr #[eExpr]
  let reprStrExpr ← Meta.mkAppM ``toString #[reprExpr]
  Term.synthesizeSyntheticMVarsNoPostponing
  let reprStrExpr ← instantiateMVars reprStrExpr

  -- Abstract over ALL locals as lambdas (not lets).
  -- Do-notation let-bindings have `nondep := false`, so `mkLambdaFVars` would
  -- create `letE` for them. We temporarily set `nondep := true` so that
  -- `generalizeNondepLet` (the default) turns them all into lambdas.
  let lctx' := localDecls.foldl (init := ← getLCtx) fun lctx decl =>
    lctx.modifyLocalDecl decl.fvarId (·.setNondep true)
  let (abstractedValue, abstractedType) ← withLCtx' lctx' do
    let abstractedValue ← Meta.mkLambdaFVars localFVars reprStrExpr
    let abstractedType ← Meta.inferType abstractedValue
    return (← instantiateMVars abstractedValue, ← instantiateMVars abstractedType)

  if abstractedValue.hasMVar then
    throwError "idbg: abstracted value still has metavariables"
  if abstractedType.hasMVar then
    throwError "idbg: abstracted type still has metavariables"

  -- Server mode: serialize and serve in a background snapshot task.
  -- Skip if expression contains sorry (partial input during editing).
  if Elab.inServer.get (← getOptions) && !abstractedValue.hasSorry then
    let json := Json.mkObj [
      ("type", exprToJson abstractedType),
      ("value", exprToJson abstractedValue)
    ]
    let cancelTk ← IO.CancelToken.new
    let act ← Core.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun () => do
      if let some result ← idbgServer siteId json then
        logInfoAt ref m!"idbg: {result}"
    Core.logSnapshotTask {
      stx? := some ref
      task := (← BaseIO.asTask (act ()))
      cancelTk? := cancelTk
    }

  -- Generate runtime code: `idbgClientLoop siteId imports apply >>= fun _ => body`
  let siteLit := Syntax.mkStrLit siteId
  let applyClosure ← withLocalDecl `f .default abstractedType fun fVar => do
    let appBody := mkAppN fVar localFVars
    Meta.mkLambdaFVars #[fVar] appBody
  let closureStx ← Term.exprToSyntax applyClosure
  -- Include the current module so the client can access same-file declarations.
  -- The `.olean` should exist since the program was compiled from it.
  let imports := (← getEnv).header.imports.push { module := (← getEnv).mainModule }
  let importExprs ← imports.mapM fun imp => do
    let nameExpr := toExpr imp.module
    let importAllExpr := toExpr imp.importAll
    let isExportedExpr := toExpr imp.isExported
    let isMetaExpr := toExpr imp.isMeta
    return mkAppN (.const ``Import.mk []) #[nameExpr, importAllExpr, isExportedExpr, isMetaExpr]
  let importsExpr := mkApp2 (.const ``List.toArray [.zero])
    (.const ``Import [])
    (importExprs.toList.foldr (fun e acc => mkApp3 (.const ``List.cons [.zero]) (.const ``Import []) e acc)
      (mkApp (.const ``List.nil [.zero]) (.const ``Import [])))
  let importsStx ← Term.exprToSyntax importsExpr
  Term.elabTerm (← `(
    Lean.Idbg.idbgClientLoop $siteLit $importsStx $closureStx >>= fun _ => $body
  )) expectedType?

@[builtin_term_elab Lean.Parser.Term.idbg]
def elabIdbgTerm : TermElab := fun stx expectedType? => do
  let `(Lean.Parser.Term.idbg| idbg $e; $body) := stx | throwUnsupportedSyntax
  elabIdbgCore (e := e) (body := body) (ref := stx) expectedType?

@[builtin_doElem_elab Lean.Parser.Term.doIdbg]
def elabDoIdbg : DoElab := fun stx dec => do
  let `(Lean.Parser.Term.doIdbg| idbg%$tk $e) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadicType (← read).doBlockResultType
  let dec ← dec.ensureUnitAt tk
  doElabToSyntax "idbg body" dec.continueWithUnit fun body => do
    elabIdbgCore (e := e) (body := body) (ref := stx) mγ

end Lean.Elab.Do

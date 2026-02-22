/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Elab.Term
import Lean.AddDecl
import Lean.Environment
import Lean.Data.Json
import Lean.Compiler.IR.CompilerM
import Init.System.IO
import Std.Internal.Async
import Std.Net.Addr

open Lean Lean.Elab Lean.Elab.Term Lean.Meta
open Std.Net Std.Internal.IO.Async

namespace Lean.Idbg

/-! ## Part 1: Expr JSON Serialization -/

public section

-- Custom Name serialization that preserves the exact structure.
-- The standard ToJson/FromJson Name uses toString/toName which doesn't
-- round-trip for hygienic names (e.g., `_@` contains `@` which isn't isIdRest).
def nameToJson : Name → Json
  | .anonymous => Json.null
  | .str p s   => Json.mkObj [("str", Json.arr #[nameToJson p, toJson s])]
  | .num p n   => Json.mkObj [("num", Json.arr #[nameToJson p, n])]

partial def nameFromJson? (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  if let some arr := (j.getObjVal? "str").toOption then
    let #[p, s] := (← fromJson? arr : Array Json) | .error "str expects 2 elements"
    return .str (← nameFromJson? p) (← fromJson? s)
  if let some arr := (j.getObjVal? "num").toOption then
    let #[p, n] := (← fromJson? arr : Array Json) | .error "num expects 2 elements"
    return .num (← nameFromJson? p) (← fromJson? n)
  .error s!"expected Name, got {j}"

def binderInfoToJson : BinderInfo → Json
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

def binderInfoFromJson? : Json → Except String BinderInfo
  | .str "default"        => .ok .default
  | .str "implicit"       => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit"   => .ok .instImplicit
  | j => .error s!"expected BinderInfo, got {j}"

def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("natVal", n)]
  | .strVal s => Json.mkObj [("strVal", s)]

def literalFromJson? (j : Json) : Except String Literal := do
  if let some n := (j.getObjVal? "natVal").toOption then
    return .natVal (← fromJson? n)
  if let some s := (j.getObjVal? "strVal").toOption then
    return .strVal (← fromJson? s)
  .error s!"expected Literal, got {j}"

partial def levelToJson : Level → Json
  | .zero     => Json.mkObj [("zero", Json.null)]
  | .succ l   => Json.mkObj [("succ", levelToJson l)]
  | .max a b  => Json.mkObj [("max", Json.arr #[levelToJson a, levelToJson b])]
  | .imax a b => Json.mkObj [("imax", Json.arr #[levelToJson a, levelToJson b])]
  | .param n  => Json.mkObj [("param", nameToJson n)]
  | .mvar id  => Json.mkObj [("mvar", nameToJson id.name)]

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

instance : ToJson Expr := ⟨exprToJson⟩
instance : FromJson Expr := ⟨exprFromJson?⟩
instance : ToJson Level := ⟨levelToJson⟩
instance : FromJson Level := ⟨levelFromJson?⟩

/-! ## Part 2: TCP Helpers -/

/-- Path to the port file for a given idbg site. The server writes the
    OS-assigned port here; the client reads and deletes it. -/
def idbgPortPath (siteId : String) : System.FilePath :=
  "/tmp" / s!"lean-idbg-{siteId}"

end -- public section

private def sendMsg (client : TCP.Socket.Client) (msg : String) : IO Unit := do
  let bytes := msg.toUTF8
  let header := (String.ofList (Nat.toDigits 16 bytes.size |>.leftpad 8 '0')).toUTF8
  let t ← (client.sendAll #[header, bytes]).toIO
  t.block

private def recvMsg (client : TCP.Socket.Client) : IO String := do
  -- Read 8-byte hex length header
  let mut header := ByteArray.empty
  while header.size < 8 do
    let t ← (client.recv? (8 - header.size).toUInt64).toIO
    let some chunk ← t.block | throw (.userError "idbg: connection closed")
    header := header ++ chunk
  let some lenStr := String.fromUTF8? header | throw (.userError "idbg: invalid header")
  let hexVal (c : Char) : Nat :=
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
    else 0
  let len := lenStr.foldl (fun acc c => acc * 16 + hexVal c) 0
  -- Read payload
  let mut payload := ByteArray.empty
  while payload.size < len do
    let t ← (client.recv? (len - payload.size).toUInt64).toIO
    let some chunk ← t.block | throw (.userError "idbg: connection closed")
    payload := payload ++ chunk
  let some s := String.fromUTF8? payload | throw (.userError "idbg: invalid UTF-8")
  return s

/-! ## Part 3: Server Side -/

public section

/-- Start a TCP server on an OS-assigned port, write it to a port file,
    wait for one connection, send expression JSON, receive result. -/
def idbgServer (siteId : String) (exprJson : Json) : IO String := do
  let server ← TCP.Socket.Server.mk
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.bind addr
  server.listen 1
  let boundAddr ← server.getSockName
  let portFile := idbgPortPath siteId
  IO.FS.writeFile portFile (toString boundAddr.port)
  try
    let t ← server.accept |>.toIO
    let client ← t.block
    sendMsg client exprJson.compress
    let result ← recvMsg client
    let t ← client.shutdown |>.toIO
    t.block
    return result
  finally
    try IO.FS.removeFile portFile catch _ => pure ()

end -- public section

/-! ## Part 4: Program-Side Eval -/

builtin_initialize idbgBaseEnvRef : IO.Ref (Option Environment) ← IO.mkRef none

/-- Load the program's environment from its imports, caching the result. -/
private unsafe def idbgGetBaseEnv (imports : Array Import) : IO Environment := do
  if let some env ← idbgBaseEnvRef.get then
    return env
  let env ← importModules imports {} 0
  idbgBaseEnvRef.set (some env)
  return env

/-- Compile and evaluate an expression in the given environment. -/
private unsafe def idbgCompileAndEval (α : Type) [Nonempty α]
    (env : Environment) (type value : Expr) : IO α := do
  let name := .mkNum `_idbg (← IO.rand 0 1000000)
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
  match env'.evalConst α {} name (checkMeta := false) with
  | .ok val => return val
  | .error msg => throw (.userError s!"idbg evalConst failed: {msg}")

/-! ## Part 5: Program-Side Client Loop -/

/-- Connect to the debug server, receive expressions, evaluate, send results. Loops forever. -/
private unsafe def idbgClientLoopUnsafe {α : Type} [Nonempty α]
    (siteId : String) (imports : Array Import) (apply : α → String) : IO Unit := do
  let baseEnv ← idbgGetBaseEnv imports
  let portFile := idbgPortPath siteId
  while true do
    try
      -- Wait for port file (silently)
      let mut portStr := ""
      for _ in List.range 6000 do  -- up to 10 minutes
        match (← IO.FS.readFile portFile |>.toBaseIO) with
        | .ok content =>
          portStr := content.trimAscii.toString
          -- Delete port file so we don't reuse it on next iteration
          try IO.FS.removeFile portFile catch _ => pure ()
          break
        | .error _ => IO.sleep 100
      if portStr.isEmpty then continue
      let port := portStr.toNat!
      -- Connect
      let client ← TCP.Socket.Client.mk
      let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port.toUInt16
      let t ← (client.connect addr).toIO
      t.block
      -- Receive expression
      let msg ← recvMsg client
      let json ← IO.ofExcept (Json.parse msg)
      let type ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "type")))
      let value ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "value")))
      -- Compile and evaluate
      let fnVal ← idbgCompileAndEval α baseEnv type value
      let result := apply fnVal
      -- Send result
      sendMsg client result
      let t ← client.shutdown |>.toIO
      t.block
    catch e =>
      -- Only log non-connection errors (connection refused is normal during reconnect)
      let msg := toString e
      unless (msg.find? "connection refused").isSome do
        IO.eprintln s!"idbg client: {e}"
      IO.sleep 500

public section

@[implemented_by idbgClientLoopUnsafe]
opaque idbgClientLoop {α : Type} [Nonempty α]
    (siteId : String) (imports : Array Import) (apply : α → String) : IO Unit

end

/-! ## Part 6: Syntax + Elaboration -/

end Lean.Idbg

namespace Lean.Elab.Do

open Lean.Idbg

syntax (name := idbg_stx) "idbg " term : doElem

@[builtin_doElem_control_info idbg_stx]
def controlInfoIdbg : ControlInfoHandler := fun _ => return default

@[builtin_doElem_elab idbg_stx]
def elabIdbg : DoElab := fun stx dec => do
  let `(doElem| idbg $e) := stx | throwUnsupportedSyntax
  -- Canonicalize the filename so the editor (absolute path) and the compiled
  -- program (possibly relative path) produce the same siteId.
  let fileName ← IO.FS.realPath (← getFileName)
  let siteId := toString (hash s!"{fileName}:{stx.raw.getPos?.getD 0}")

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

  -- Elaborate e, wrap in toString.
  -- synthesizeSyntheticMVarsNoPostponing forces pending instance resolution
  -- so that instantiateMVars can fully resolve all metavariables.
  let eExpr ← Term.elabTerm e none
  Term.synthesizeSyntheticMVarsNoPostponing
  let eExpr ← instantiateMVars eExpr
  let toStringExpr ← Meta.mkAppM ``toString #[eExpr]
  Term.synthesizeSyntheticMVarsNoPostponing
  let toStringExpr ← instantiateMVars toStringExpr

  -- Abstract over ALL locals as lambdas (not lets).
  -- We can't use mkLambdaFVars because it creates letE for let-bound locals
  -- (when their nondep flag is false, as in do-notation), but we need lambdas
  -- so the running program can pass its own values for these variables.
  let abstractedValue := toStringExpr.abstract localFVars
  let abstractedValue ← localFVars.size.foldRevM (init := abstractedValue) fun i _ acc => do
    let decl := localDecls[i]!
    let type ← instantiateMVars (← Meta.inferType (mkFVar decl.fvarId))
    let type := type.abstract (localFVars[:i])
    return .lam decl.userName type acc .default
  let abstractedType ← instantiateMVars (← Meta.inferType abstractedValue)

  -- Sanity check: no metavariables should remain
  if abstractedValue.hasMVar then
    throwError "idbg: abstracted value still has metavariables"
  if abstractedType.hasMVar then
    throwError "idbg: abstracted type still has metavariables"

  -- Server mode: serialize and serve
  if Elab.inServer.get (← getOptions) then
    let json := Json.mkObj [
      ("type", exprToJson abstractedType),
      ("value", exprToJson abstractedValue)
    ]
    let result ← idbgServer siteId json
    logInfoAt stx m!"idbg: {result}"

  -- Generate runtime code for compiled execution
  let mγ ← mkMonadicType (← read).doBlockResultType
  doElabToSyntax "idbg body" dec.continueWithUnit fun body => do
    let siteLit := Syntax.mkStrLit siteId
    -- Build the apply closure: fun (f : abstractedType) => f x₁ x₂ ...
    let applyClosure ← withLocalDecl `f .default abstractedType fun fVar => do
      let appBody := mkAppN fVar localFVars
      Meta.mkLambdaFVars #[fVar] appBody
    let closureStx ← Term.exprToSyntax applyClosure
    -- Build imports array from current environment so the client can
    -- reconstruct an environment with all necessary constants.
    let imports := (← getEnv).header.imports
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
    )) mγ

end Lean.Elab.Do

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.AddDecl
public import Lean.Data.Json
public import Std.Async.TCP

/-!
# Runtime support for the interactive debug expression evaluator (`idbg`)

`idbg` enables live communication between a running compiled Lean program and the language server.
This module contains the parts used by the compiled program, whose entry point
`Lean.Idbg.idbgClientLoop` is declared in `Lean.Setup`. The elaborator is in `Lean.Elab.Idbg`.

## Protocol

Communication uses a length-prefixed TCP protocol over localhost. Both server (language server side)
and client (compiled program side) compute a deterministic port from the source location hash.
-/

public section

open Lean
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

end

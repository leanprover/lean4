module

import Lean
import all Lean.Elab.Idbg
import Std.Async
import Std.Net.Addr

/-! ## Part 1: Expr JSON round-trip with hygienic names -/

open Lean Lean.Idbg Std.Net Std.Async in
#eval show IO Unit from do
  -- `_@` contains `@` which breaks the standard Name.toString/toName round-trip
  let hygName := Name.mkNum (.mkStr (.mkNum (.mkStr (.mkStr .anonymous "_@") "test") 42) "_hyg") 6

  -- Lambda with hygienic name
  let e := Expr.lam hygName (.const ``Nat []) (.bvar 0) .default
  let j := exprToJson e
  let d ← IO.ofExcept (exprFromJson? j)
  let Expr.lam n .. := d | throw (IO.userError "expected lam")
  assert! n == hygName

  -- Const with universe levels
  let e2 := Expr.const ``List [.param `u]
  let j2 := exprToJson e2
  let d2 ← IO.ofExcept (exprFromJson? j2)
  let Expr.const n2 ls2 := d2 | throw (IO.userError "expected const")
  assert! n2 == ``List
  assert! ls2 == [.param `u]

-- The remainder of the test currently is a bit timing- and possibly platform-dependent, better for
-- selective testing locally than in CI
#exit

/-! ## Part 2: Manual TCP server/client round-trip with hand-built expression -/

open Lean Lean.Idbg Std.Net Std.Async in
#eval show IO Unit from do
  let siteId := "test-e2e"
  let env ← importModules #[{ module := `Init }] {} 0

  -- Build: fun (x : Nat) => toString (Nat.add x 1)
  let value := Expr.lam `x (.const ``Nat []) (mkApp3 (.const ``ToString.toString [.zero])
    (.const ``Nat [])
    (.const ``instToStringNat [])
    (mkApp2 (.const ``Nat.add []) (.bvar 0) (mkNatLit 1))) .default
  let type := Expr.forallE `x (.const ``Nat []) (.const ``String []) .default

  let exprJson := Json.mkObj [
    ("type", exprToJson type),
    ("value", exprToJson value)
  ]

  -- Run server in background
  let serverTask ← IO.asTask (idbgServer siteId exprJson)

  -- Give server time to bind
  IO.sleep 100

  -- Connect to deterministic port
  let port := idbgPort siteId
  let client ← TCP.Socket.Client.mk
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port
  let t ← (client.connect addr).toIO
  t.block

  -- Receive length-prefixed message (decimal length + newline + payload)
  let mut hdr := ByteArray.empty
  repeat
    let t ← (client.recv? 1).toIO
    let some chunk ← t.block | throw (IO.userError "connection closed")
    if chunk[0]! == '\n'.toUInt8 then break
    hdr := hdr ++ chunk
  let some hdrStr := String.fromUTF8? hdr | throw (IO.userError "invalid header")
  let some len := hdrStr.toNat? | throw (IO.userError "invalid length")
  let mut payload := ByteArray.empty
  while payload.size < len do
    let t ← (client.recv? (len - payload.size).toUInt64).toIO
    let some chunk ← t.block | throw (IO.userError "connection closed")
    payload := payload ++ chunk
  let some msg := String.fromUTF8? payload | throw (IO.userError "invalid UTF-8")

  -- Parse and compile
  let json ← IO.ofExcept (Json.parse msg)
  let recvType ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "type")))
  let recvValue ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "value")))

  let declName := `_idbg_test
  let decl := Declaration.defnDecl {
    name := declName
    levelParams := []
    type := recvType
    value := recvValue
    hints := .opaque
    safety := .unsafe
  }
  let ((), {env := env', ..}) ← (addAndCompile decl).toIO
    { fileName := "<idbg-test>", fileMap := default, options := {} }
    { env }
  let result := match env'.evalConst (Nat → String) {} declName (checkMeta := false) with
    | .ok f => f 41  -- 41 + 1 = 42
    | .error msg => s!"evalConst failed: {msg}"

  -- Send result back (length-prefixed)
  let resultBytes := result.toUTF8
  let resultHdr := s!"{resultBytes.size}\n".toUTF8
  let t ← (client.sendAll #[resultHdr, resultBytes]).toIO
  t.block
  let t ← client.shutdown |>.toIO
  t.block

  -- Verify server received "42"
  let serverResult ← IO.ofExcept (← IO.wait serverTask)
  assert! serverResult == some "42"

/-! ## Part 3: Full pipeline through the real elaborator

Run `lean -DElab.inServer=true` on a file containing `idbg`, then act as the
client: receive the expression JSON, compile it, evaluate it, send result back.
This is the actual end-to-end flow that happens between the editor and a running program.
We do this TWICE to test reconnection (simulating the user editing the expression). -/

open Lean Lean.Idbg Std.Net Std.Async in
#eval show IO Unit from do
  let lean := (← IO.appDir) / "lean"
  let env ← importModules #[{ module := `Init }] {} 0

  -- Helper: run lean on a test file with idbg, act as client, compile the received expression
  let doExchange := fun (env : Environment) (testCode : String) (idbgPos : Nat) => do
    IO.FS.withTempFile fun _ testFile => do
    IO.FS.writeFile testFile testCode
    let realPath ← IO.FS.realPath testFile
    let siteId := toString (hash s!"{realPath}:{idbgPos}")
    let port := idbgPort siteId

    let child ← IO.Process.spawn {
      cmd := lean.toString
      args := #["-DElab.inServer=true", testFile.toString]
      stdout := .piped
      stderr := .piped
    }

    -- Retry connecting until the server binds
    let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port
    let mut client ← TCP.Socket.Client.mk
    let mut connected := false
    for _ in List.range 200 do
      match (← (do let t ← (client.connect addr).toIO; t.block : IO Unit).toBaseIO) with
      | .ok () => connected := true; break
      | .error _ => IO.sleep 100; client ← TCP.Socket.Client.mk
    unless connected do
      let stderr ← child.stderr.readToEnd
      throw (IO.userError s!"Could not connect to port {port}. stderr: {stderr}")

    -- Receive expression JSON (length-prefixed: decimal length + newline + payload)
    let mut hdr := ByteArray.empty
    repeat
      let t ← (client.recv? 1).toIO
      let some chunk ← t.block | throw (IO.userError "connection closed")
      if chunk[0]! == '\n'.toUInt8 then break
      hdr := hdr ++ chunk
    let some hdrStr := String.fromUTF8? hdr | throw (IO.userError "invalid header")
    let some len := hdrStr.toNat? | throw (IO.userError "invalid length")
    let mut payload := ByteArray.empty
    while payload.size < len do
      let t ← (client.recv? (len - payload.size).toUInt64).toIO
      let some chunk ← t.block | throw (IO.userError "connection closed")
      payload := payload ++ chunk
    let some msg := String.fromUTF8? payload | throw (IO.userError "invalid UTF-8")

    let json ← IO.ofExcept (Json.parse msg)
    let recvType ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "type")))
    let recvValue ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "value")))

    -- Verify no metavariables
    if recvValue.hasMVar then throw (IO.userError "Expression value has metavariables!")
    if recvType.hasMVar then throw (IO.userError "Expression type has metavariables!")

    -- Compile (this is where "declaration has metavariables" would fail)
    let declName := `_idbg_e2e_real
    let decl := Declaration.defnDecl {
      name := declName
      levelParams := []
      type := recvType
      value := recvValue
      hints := .opaque
      safety := .unsafe
    }
    let _ ← (addAndCompile decl).toIO
      { fileName := "<idbg-test>", fileMap := default, options := {} }
      { env }

    -- Send dummy result back (length-prefixed)
    let resultBytes := "test-ok".toUTF8
    let resultHdr := s!"{resultBytes.size}\n".toUTF8
    let t ← (client.sendAll #[resultHdr, resultBytes]).toIO
    t.block
    let t ← client.shutdown |>.toIO
    t.block
    let _ ← child.wait

  -- Exchange 1: `idbg x + s.length`
  -- idbg at byte 108 in this string
  let code1 := "import Lean\nset_option backward.do.legacy false\ndef main : IO Unit := do\n  let x := 42\n  let s := \"hello\"\n  idbg x + s.length\n"
  doExchange env code1 108

  -- Exchange 2: `idbg x + s.length + 1` (the expression that triggered the mvar bug)
  -- idbg at byte 108 in this string too
  let code2 := "import Lean\nset_option backward.do.legacy false\ndef main : IO Unit := do\n  let x := 42\n  let s := \"hello\"\n  idbg x + s.length + 1\n"
  doExchange env code2 108

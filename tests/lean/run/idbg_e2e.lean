module

import Lean
import Std.Internal.Async
import Std.Net.Addr

/-! ## Part 1: Expr JSON round-trip with hygienic names -/

open Lean Lean.Idbg Std.Net Std.Internal.IO.Async in
#eval show IO Unit from do
  -- `_@` contains `@` which breaks the standard Name.toString/toName round-trip
  let hygName := Name.mkNum (.mkStr (.mkNum (.mkStr (.mkStr .anonymous "_@") "test") 42) "_hyg") 6

  -- Lambda with hygienic name
  let e := Expr.lam hygName (.const ``Nat []) (.bvar 0) .default
  let j := toJson (α := Expr) e
  let d ← IO.ofExcept (fromJson? j : Except String Expr)
  let Expr.lam n .. := d | throw (IO.userError "expected lam")
  assert! n == hygName

  -- Const with universe levels
  let e2 := Expr.const ``List [.param `u]
  let j2 := toJson (α := Expr) e2
  let d2 ← IO.ofExcept (fromJson? j2 : Except String Expr)
  let Expr.const n2 ls2 := d2 | throw (IO.userError "expected const")
  assert! n2 == ``List
  assert! ls2 == [.param `u]

/-! ## Part 2: Manual TCP server/client round-trip with hand-built expression -/

open Lean Lean.Idbg Std.Net Std.Internal.IO.Async in
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
    ("type", toJson (α := Expr) type),
    ("value", toJson (α := Expr) value)
  ]

  -- Run server in background
  let serverTask ← IO.asTask (idbgServer siteId exprJson)

  -- Give server time to start and write port file
  IO.sleep 100

  -- Read port from file
  let portFile := idbgPortPath siteId
  let portStr ← IO.FS.readFile portFile
  let port := portStr.trimAscii.toString.toNat!
  let client ← TCP.Socket.Client.mk
  let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port.toUInt16
  let t ← (client.connect addr).toIO
  t.block

  -- Receive expression JSON (length-prefixed: 8 hex digits + payload)
  let mut header := ByteArray.empty
  while header.size < 8 do
    let t ← (client.recv? (8 - header.size).toUInt64).toIO
    let some chunk ← t.block | throw (IO.userError "connection closed reading header")
    header := header ++ chunk
  let some lenStr := String.fromUTF8? header | throw (IO.userError "invalid header")
  let hexVal (c : Char) : Nat :=
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
    else 0
  let len := lenStr.foldl (fun acc c => acc * 16 + hexVal c) 0
  let mut payload := ByteArray.empty
  while payload.size < len do
    let t ← (client.recv? (len - payload.size).toUInt64).toIO
    let some chunk ← t.block | throw (IO.userError "connection closed reading payload")
    payload := payload ++ chunk
  let some msg := String.fromUTF8? payload | throw (IO.userError "invalid UTF-8")

  -- Parse and compile
  let json ← IO.ofExcept (Json.parse msg)
  let recvType ← IO.ofExcept (fromJson? (← IO.ofExcept (json.getObjVal? "type")) : Except String Expr)
  let recvValue ← IO.ofExcept (fromJson? (← IO.ofExcept (json.getObjVal? "value")) : Except String Expr)

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
  let bytes := result.toUTF8
  let hdr := (String.ofList (Nat.toDigits 16 bytes.size |>.leftpad 8 '0')).toUTF8
  let t ← (client.sendAll #[hdr, bytes]).toIO
  t.block
  let t ← client.shutdown |>.toIO
  t.block

  -- Verify server received "42"
  let serverResult ← IO.ofExcept (← IO.wait serverTask)
  assert! serverResult == "42"

/-! ## Part 3: Full pipeline through the real elaborator

Run `lean -DElab.inServer=true` on a file containing `idbg`, then act as the
client: receive the expression JSON, compile it, evaluate it, send result back.
This is the actual end-to-end flow that happens between the editor and a running program.
We do this TWICE to test reconnection (simulating the user editing the expression). -/

open Lean Lean.Idbg Std.Net Std.Internal.IO.Async in
#eval show IO Unit from do
  let lean := (← IO.appDir) / "lean"
  let env ← importModules #[{ module := `Init }] {} 0

  -- Helper: run lean on a test file with idbg, act as client, compile the received expression
  let doExchange := fun (env : Environment) (testCode : String) (idbgPos : Nat) => do
    let testFile : System.FilePath := "/tmp" / "idbg_e2e_test.lean"
    IO.FS.writeFile testFile testCode
    let realPath ← IO.FS.realPath testFile
    let siteId := toString (hash s!"{realPath}:{idbgPos}")
    let portFile := idbgPortPath siteId
    -- Clean up stale port file
    try IO.FS.removeFile portFile catch _ => pure ()

    let child ← IO.Process.spawn {
      cmd := lean.toString
      args := #["-DElab.inServer=true", testFile.toString]
      stdout := .piped
      stderr := .piped
    }

    -- Poll for port file, then connect
    let mut port : Nat := 0
    for _ in List.range 200 do
      IO.sleep 100
      let content ← try IO.FS.readFile portFile catch _ => continue
      let p := String.trimAscii content |>.toString |>.toNat!
      if p > 0 then port := p; break
    if port == 0 then
      let stderr ← child.stderr.readToEnd
      throw (IO.userError s!"Port file not found. stderr: {stderr}")
    let client ← TCP.Socket.Client.mk
    let addr := SocketAddressV4.mk (.ofParts 127 0 0 1) port.toUInt16
    let t ← (client.connect addr).toIO
    t.block

    -- Receive expression JSON
    let mut header := ByteArray.empty
    while header.size < 8 do
      let t ← (client.recv? (8 - header.size).toUInt64).toIO
      let some chunk ← t.block | throw (IO.userError "connection closed reading header")
      header := header ++ chunk
    let some lenStr := String.fromUTF8? header | throw (IO.userError "invalid header")
    let hexVal (c : Char) : Nat :=
      if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else 0
    let len := lenStr.foldl (fun acc c => acc * 16 + hexVal c) 0
    let mut payload := ByteArray.empty
    while payload.size < len do
      let t ← (client.recv? (len - payload.size).toUInt64).toIO
      let some chunk ← t.block | throw (IO.userError "connection closed reading payload")
      payload := payload ++ chunk
    let some msg := String.fromUTF8? payload | throw (IO.userError "invalid UTF-8")

    let json ← IO.ofExcept (Json.parse msg)
    let recvType ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "type")))
    let recvValue ← IO.ofExcept (exprFromJson? (← IO.ofExcept (json.getObjVal? "value")))

    -- Verify no metavariables
    if recvValue.hasMVar then throw (IO.userError "Expression value has metavariables!")
    if recvType.hasMVar then throw (IO.userError "Expression type has metavariables!")

    -- Compile (this is where "declaration has metavariables" would fail)
    let declName := .mkNum `_idbg_e2e_real (← IO.rand 0 1000000)
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

    -- Send dummy result back
    let bytes := "test-ok".toUTF8
    let hdr := (String.ofList (Nat.toDigits 16 bytes.size |>.leftpad 8 '0')).toUTF8
    let t ← (client.sendAll #[hdr, bytes]).toIO
    t.block
    let t ← client.shutdown |>.toIO
    t.block
    let _ ← child.wait
    return env'

  -- Exchange 1: `idbg x + s.length`
  -- idbg at byte 108 in this string
  let code1 := "import Lean\nset_option backward.do.legacy false\ndef main : IO Unit := do\n  let x := 42\n  let s := \"hello\"\n  idbg x + s.length\n"
  let env' ← doExchange env code1 108

  -- Exchange 2: `idbg x + s.length + 1` (the expression that triggered the mvar bug)
  -- idbg at byte 108 in this string too
  let code2 := "import Lean\nset_option backward.do.legacy false\ndef main : IO Unit := do\n  let x := 42\n  let s := \"hello\"\n  idbg x + s.length + 1\n"
  let _ ← doExchange env' code2 108

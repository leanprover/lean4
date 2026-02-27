import Lean

open Lean Lsp

private def assert (b : Bool) (msg : String := "assertion failed") : IO Unit :=
  if b then pure () else throw <| IO.userError msg

-- Round-trip `InitializationOptions` with `options?` through JSON.
#guard_msgs in
#eval do
  let opts : LeanOptions := LeanOptions.ofArray #[
    { name := `pp.all, value := .ofBool false },
    { name := `server.reportDelayMs, value := .ofNat 200 }
  ]
  let initOpts : InitializationOptions := {
    hasWidgets? := some true
    logCfg? := none
    options? := some opts
  }
  let json := toJson initOpts
  let parsed ← IO.ofExcept <| (fromJson? json : Except String InitializationOptions)
  assert (parsed.hasWidgets? == some true) "hasWidgets? mismatch"
  let parsedOpts := parsed.options?.get!
  let kvs := parsedOpts.toOptions
  assert (pp.all.get kvs == false) "pp.all mismatch"

-- `InitializationOptions` without `options?` still parses.
#guard_msgs in
#eval do
  let initOpts : InitializationOptions := {
    hasWidgets? := none
    logCfg? := none
  }
  let json := toJson initOpts
  let parsed ← IO.ofExcept <| (fromJson? json : Except String InitializationOptions)
  assert (parsed.options?.isNone) "options? should be none"

-- Parse `InitializationOptions` from a raw JSON object with options.
#guard_msgs in
#eval do
  let json := Json.mkObj [
    ("hasWidgets", Json.bool true),
    ("options", Json.mkObj [
      ("pp.all", Json.bool false),
      ("pp.unicode", Json.bool true)
    ])
  ]
  let parsed ← IO.ofExcept <| (fromJson? json : Except String InitializationOptions)
  assert (parsed.hasWidgets? == some true) "hasWidgets? mismatch"
  let parsedOpts := parsed.options?.get!
  let kvs := parsedOpts.toOptions
  assert (pp.all.get kvs == false) "pp.all mismatch"
  assert (pp.unicode.get kvs == true) "pp.unicode mismatch"

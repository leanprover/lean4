import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.Outgoing)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

instance : Coe (ContextAsync (Response Body.Incoming)) (ContextAsync (Response Body.Outgoing)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

instance : Coe (Async (Response Body.Incoming)) (ContextAsync (Response Body.Outgoing)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

def defaultConfig : Config :=
  { lingeringTimeout := 500, generateDate := false }

def runWithTimeout {α : Type} (name : String) (timeoutMs : Nat := 2000) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let ticks := (timeoutMs + 9) / 10

  let rec loop (remaining : Nat) : IO α := do
    if (← IO.getTaskState task) == .finished then
      match (← IO.wait task) with
      | .ok x => pure x
      | .error err => throw err
    else
      match remaining with
      | 0 =>
        IO.cancel task
        throw <| IO.userError s!"Test '{name}' timed out after {timeoutMs}ms (possible hang/loop)"
      | n + 1 =>
        IO.sleep 10
        loop n

  loop ticks

def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : TestHandler) (config : Config := defaultConfig) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty

def sendRawTimed (name : String) (raw : ByteArray)
    (handler : TestHandler) (config : Config := defaultConfig) : IO ByteArray :=
  runWithTimeout name 2000 do
    let (client, server) ← Mock.new
    sendRaw client server raw handler config

def runClosedClientTimed (name : String) (raw : ByteArray)
    (handler : TestHandler) (config : Config := defaultConfig) : IO Unit :=
  runWithTimeout name 2000 do
    Async.block do
      let (client, server) ← Mock.new
      client.send raw
      client.close
      Std.Http.Server.serveConnection server handler config
        |>.run

def countOccurrences (s : String) (needle : String) : Nat :=
  if needle.isEmpty then 0 else (s.splitOn needle).length - 1

def assertStatusPrefix (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected prefix: {prefix_.quote}\nGot:\n{text.quote}"

def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nMissing: {needle.quote}\nGot:\n{text.quote}"

def assertEndsWith (name : String) (response : ByteArray) (suffix_ : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.endsWith suffix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected suffix: {suffix_.quote}\nGot:\n{text.quote}"

def assertStatusCount (name : String) (response : ByteArray) (expected : Nat) : IO Unit := do
  let text := String.fromUTF8! response
  let got := countOccurrences text "HTTP/1.1 "
  unless got == expected do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} HTTP responses, got {got}\n{text.quote}"

def onesChunked (n : Nat) : String := Id.run do
  let mut body := ""
  for _ in [0:n] do
    body := body ++ "1\x0d\na\x0d\n"
  body ++ "0\x0d\n\x0d\n"

def ignoreHandler : TestHandler := fun _ => Response.ok |>.text "ok"

def uriHandler : TestHandler := fun req => Response.ok |>.text (toString req.head.uri)

def echoBodyHandler : TestHandler := fun req => do
  let mut body := ByteArray.empty
  for chunk in req.body do
    body := body ++ chunk.data
  Response.ok |>.text (String.fromUTF8! body)

def firstChunkHandler : TestHandler := fun req => do
  let first ← req.body.recv none
  let text :=
    match first with
    | some chunk => String.fromUTF8! chunk.data
    | none => "none"
  Response.ok |>.text text

def streamPiecesHandler (n : Nat) : TestHandler := fun _ => do
  let (outgoing, _incoming) ← Body.mkChannel
  background do
    for i in [0:n] do
      outgoing.send <| Chunk.ofByteArray s!"piece-{i};".toUTF8
    outgoing.close
  return Response.ok
    |>.body outgoing

def stressResponseHandler (n : Nat) : TestHandler := fun _ => do
  let (outgoing, _incoming) ← Body.mkChannel
  background do
    for i in [0:n] do
      outgoing.send <| Chunk.ofByteArray s!"x{i},".toUTF8
    outgoing.close
  return Response.ok
    |>.body outgoing

-- 01: Ignore fixed-size request body and respond immediately.
#eval runWithTimeout "01_ignore_fixed_length_body" 2000 do
  let raw := "POST /fixed HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\n\x0d\n0123456789".toUTF8
  let response ← sendRawTimed "01_ignore_fixed_length_body/send" raw ignoreHandler
  assertStatusPrefix "01_ignore_fixed_length_body" response "HTTP/1.1 200"

-- 02: Ignore chunked request body and respond immediately.
#eval runWithTimeout "02_ignore_chunked_body" 2000 do
  let raw := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n6\x0d\n world\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRawTimed "02_ignore_chunked_body/send" raw ignoreHandler
  assertStatusPrefix "02_ignore_chunked_body" response "HTTP/1.1 200"

-- 03: Large fixed-size body ignored by handler (regression for stalled body transfer).
#eval runWithTimeout "03_ignore_large_fixed_body" 2000 do
  let body := String.ofList (List.replicate 8192 'A')
  let raw := s!"POST /large HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 8192\x0d\nConnection: close\x0d\n\x0d\n{body}".toUTF8
  let response ← sendRawTimed "03_ignore_large_fixed_body/send" raw ignoreHandler
  assertStatusPrefix "03_ignore_large_fixed_body" response "HTTP/1.1 200"

-- 04: Read full request body and echo it.
#eval runWithTimeout "04_echo_full_body" 2000 do
  let raw := "POST /echo HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 11\x0d\nConnection: close\x0d\n\x0d\nhello world".toUTF8
  let response ← sendRawTimed "04_echo_full_body/send" raw echoBodyHandler
  assertContains "04_echo_full_body" response "hello world"

-- 05: Read only first chunk and reply (should not deadlock connection).
#eval runWithTimeout "05_read_first_chunk_only" 2000 do
  let raw := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 11\x0d\nConnection: close\x0d\n\x0d\nhello world".toUTF8
  let response ← sendRawTimed "05_read_first_chunk_only/send" raw firstChunkHandler
  assertStatusPrefix "05_read_first_chunk_only" response "HTTP/1.1 200"
  assertContains "05_read_first_chunk_only" response "hello world"

-- 06: Stream many response chunks.
#eval runWithTimeout "06_stream_many_response_chunks" 2000 do
  let raw := "GET /stream HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRawTimed "06_stream_many_response_chunks/send" raw (streamPiecesHandler 40)
  assertStatusPrefix "06_stream_many_response_chunks" response "HTTP/1.1 200"
  assertContains "06_stream_many_response_chunks" response "piece-0;"
  assertContains "06_stream_many_response_chunks" response "piece-39;"

-- 07: Stream response with known fixed size.
#eval runWithTimeout "07_stream_known_size" 2000 do
  let raw := "GET /known HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRawTimed "07_stream_known_size/send" raw (fun _ => do
    let (outgoing, _incoming) ← Body.mkChannel
    outgoing.setKnownSize (some (.fixed 8))
    background do
      outgoing.send <| Chunk.ofByteArray "abcd".toUTF8
      outgoing.send <| Chunk.ofByteArray "efgh".toUTF8
      outgoing.close
    return Response.ok
      |>.body outgoing)
  assertStatusPrefix "07_stream_known_size" response "HTTP/1.1 200"
  assertContains "07_stream_known_size" response "Content-Length: 8"
  assertContains "07_stream_known_size" response "abcdefgh"

-- 08: Use interestSelector before sending response data.
#eval runWithTimeout "08_interest_selector_gating" 2000 do
  let raw := "GET /interest HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRawTimed "08_interest_selector_gating/send" raw (fun _ => do
    let (outgoing, _incoming) ← Body.mkChannel
    background do
      let interested ← Selectable.one #[
        .case outgoing.interestSelector pure
      ]
      if interested then
        outgoing.send <| Chunk.ofByteArray "interest-ok".toUTF8
      outgoing.close
    return Response.ok
      |>.body outgoing)
  assertStatusPrefix "08_interest_selector_gating" response "HTTP/1.1 200"
  assertContains "08_interest_selector_gating" response "interest-ok"

-- 09: Incomplete sends collapse into one payload.
#eval runWithTimeout "09_incomplete_send_collapse" 2000 do
  let raw := "GET /collapse HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRawTimed "09_incomplete_send_collapse/send" raw (fun _ => do
    let (outgoing, _incoming) ← Body.mkChannel
    background do
      outgoing.send ({ data := "hello ".toUTF8, extensions := #[] } : Chunk) (incomplete := true)
      outgoing.send ({ data := "wor".toUTF8, extensions := #[] } : Chunk) (incomplete := true)
      outgoing.send ({ data := "ld".toUTF8, extensions := #[] } : Chunk)
      outgoing.close
    return Response.ok
      |>.body outgoing)
  assertStatusPrefix "09_incomplete_send_collapse" response "HTTP/1.1 200"
  assertContains "09_incomplete_send_collapse" response "hello world"

-- 10: Pipeline fixed-body POST then GET.
#eval runWithTimeout "10_pipeline_fixed_then_get" 2000 do
  let raw := ("POST /one HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
              "GET /two HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
  let response ← sendRawTimed "10_pipeline_fixed_then_get/send" raw uriHandler
  assertStatusCount "10_pipeline_fixed_then_get" response 2
  assertContains "10_pipeline_fixed_then_get" response "/one"
  assertContains "10_pipeline_fixed_then_get" response "/two"

-- 11: Pipeline chunked-body POST then GET.
#eval runWithTimeout "11_pipeline_chunked_then_get" 2000 do
  let raw := ("POST /chunk HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n" ++
              "GET /two HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
  let response ← sendRawTimed "11_pipeline_chunked_then_get/send" raw uriHandler
  assertStatusCount "11_pipeline_chunked_then_get" response 2
  assertContains "11_pipeline_chunked_then_get" response "/chunk"
  assertContains "11_pipeline_chunked_then_get" response "/two"

-- 12: Malformed first request should not loop into second.
#eval runWithTimeout "12_malformed_closes_connection" 2000 do
  let raw := ("GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBadHeader value\x0d\n\x0d\n" ++
              "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
  let response ← sendRawTimed "12_malformed_closes_connection/send" raw uriHandler
  assertStatusPrefix "12_malformed_closes_connection" response "HTTP/1.1 400"
  assertStatusCount "12_malformed_closes_connection" response 1

-- 13: Client closes while server is streaming response.
#eval runWithTimeout "13_client_close_while_streaming" 2000 do
  let raw := "GET /close-stream HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  runClosedClientTimed "13_client_close_while_streaming/run" raw (stressResponseHandler 600)

-- 14: Client closes before sending full body.
#eval runWithTimeout "14_client_close_mid_body" 2000 do
  let raw := "POST /mid-body HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 100\x0d\nConnection: close\x0d\n\x0d\nabcde".toUTF8
  runClosedClientTimed "14_client_close_mid_body/run" raw ignoreHandler

-- 15: Handler throws while request body is present.
#eval runWithTimeout "15_handler_throw_unread_body" 2000 do
  let raw := "POST /throw HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRawTimed "15_handler_throw_unread_body/send" raw (fun _ => throw <| IO.userError "boom")
  assertStatusPrefix "15_handler_throw_unread_body" response "HTTP/1.1 500"

-- 16: Many tiny chunked request chunks ignored by handler.
#eval runWithTimeout "16_many_tiny_chunked_ignored" 2000 do
  let body := onesChunked 80
  let raw := s!"POST /tiny HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n{body}".toUTF8
  let response ← sendRawTimed "16_many_tiny_chunked_ignored/send" raw ignoreHandler
  assertStatusPrefix "16_many_tiny_chunked_ignored" response "HTTP/1.1 200"

-- 17: Many tiny chunked request chunks consumed and counted.
#eval runWithTimeout "17_many_tiny_chunked_consumed" 2000 do
  let body := onesChunked 25
  let raw := s!"POST /count HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n{body}".toUTF8
  let response ← sendRawTimed "17_many_tiny_chunked_consumed/send" raw (fun req => do
    let mut count := 0
    for _ in req.body do
      count := count + 1
    Response.ok |>.text (toString count))
  assertStatusPrefix "17_many_tiny_chunked_consumed" response "HTTP/1.1 200"
  assertEndsWith "17_many_tiny_chunked_consumed" response "25"

-- 18: Stress response streaming with many chunks and active client.
#eval runWithTimeout "18_stress_streaming_active_client" 2000 do
  let raw := "GET /stress HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRawTimed "18_stress_streaming_active_client/send" raw (stressResponseHandler 120)
  assertStatusPrefix "18_stress_streaming_active_client" response "HTTP/1.1 200"
  assertContains "18_stress_streaming_active_client" response "x0,"
  assertContains "18_stress_streaming_active_client" response "x119,"

-- 19: Pipeline with large unread first body still processes second request.
#eval runWithTimeout "19_pipeline_large_unread_then_get" 2000 do
  let body := String.ofList (List.replicate 5000 'b')
  let raw := (s!"POST /big HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5000\x0d\n\x0d\n{body}" ++
              "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
  let response ← sendRawTimed "19_pipeline_large_unread_then_get/send" raw uriHandler
  assertStatusCount "19_pipeline_large_unread_then_get" response 2
  assertContains "19_pipeline_large_unread_then_get" response "/big"
  assertContains "19_pipeline_large_unread_then_get" response "/after"

-- 20: Triple pipeline mixed body styles.
#eval runWithTimeout "20_triple_pipeline_mixed" 2000 do
  let raw := ("POST /a HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 4\x0d\n\x0d\ndata" ++
              "POST /b HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n3\x0d\nhey\x0d\n0\x0d\n\x0d\n" ++
              "GET /c HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8
  let response ← sendRawTimed "20_triple_pipeline_mixed/send" raw uriHandler
  assertStatusCount "20_triple_pipeline_mixed" response 3
  assertContains "20_triple_pipeline_mixed" response "/a"
  assertContains "20_triple_pipeline_mixed" response "/b"
  assertContains "20_triple_pipeline_mixed" response "/c"

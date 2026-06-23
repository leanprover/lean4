import Std.Http.Data.Body

open Std.Async
open Std.Http
open Std.Http.Body

/-! ## Stream tests -/

-- Test send and recv on stream

def channelSendRecv : Async Unit := do
  let stream ← Body.mkStream
  let chunk := Chunk.ofByteArray "hello".toUTF8

  let sendTask ← async (t := AsyncTask) <| stream.send chunk
  let result ← stream.recv

  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8
  await sendTask

#eval channelSendRecv.block


-- Test tryRecv on empty stream returns none

def channelTryRecvEmpty : Async Unit := do
  let stream ← Body.mkStream
  let result ← stream.tryRecv
  assert! result.isNone

#eval channelTryRecvEmpty.block

-- Test tryRecv consumes a waiting producer

def channelTryRecvWithPendingSend : Async Unit := do
  let stream ← Body.mkStream

  let sendTask ← async (t := AsyncTask) <| stream.send (Chunk.ofByteArray "data".toUTF8)
  let mut result := none
  let mut fuel := 100
  while result.isNone && fuel > 0 do
    result ← stream.tryRecv
    if result.isNone then
      let _ ← Selectable.one #[
        .case (← Selector.sleep 1) pure
      ]
    fuel := fuel - 1

  assert! result.isSome
  assert! result.get!.data == "data".toUTF8
  await sendTask

#eval channelTryRecvWithPendingSend.block

-- Test close sets closed flag

def channelClose : Async Unit := do
  let stream ← Body.mkStream
  assert! !(← stream.isClosed)
  stream.close
  assert! (← stream.isClosed)

#eval channelClose.block

-- Test recv on closed stream returns none

def channelRecvAfterClose : Async Unit := do
  let stream ← Body.mkStream
  stream.close
  let result ← stream.recv
  assert! result.isNone

#eval channelRecvAfterClose.block

-- Test Body.stream runs producer concurrently and transfers chunks

def bodyStreamSends : Async Unit := do
  let incoming ← Body.stream fun outgoing => do
    outgoing.send (Chunk.ofByteArray "x".toUTF8)

  let first ← incoming.recv
  assert! first.isSome
  assert! first.get!.data == "x".toUTF8

  let done ← incoming.recv
  assert! done.isNone

#eval bodyStreamSends.block

-- Test Body.stream closes channel when generator throws

def bodyStreamThrowCloses : Async Unit := do
  let incoming ← Body.stream fun _ => do
    throw (.userError "boom")

  let result ← incoming.recv
  assert! result.isNone

#eval bodyStreamThrowCloses.block

-- Test for-in iteration collects chunks until close

def channelForIn : Async Unit := do
  let stream ← Body.mkStream

  let producer ← async (t := AsyncTask) <| do
    stream.send (Chunk.ofByteArray "a".toUTF8)
    stream.send (Chunk.ofByteArray "b".toUTF8)
    stream.close

  let mut acc : ByteArray := .empty
  for chunk in stream do
    acc := acc ++ chunk.data

  assert! acc == "ab".toUTF8
  await producer

#eval channelForIn.block

-- Test chunk extensions are preserved

def channelExtensions : Async Unit := do
  let stream ← Body.mkStream
  let chunk := { data := "hello".toUTF8, extensions := #[(.mk "key", some (Chunk.ExtensionValue.ofString! "value"))] : Chunk }

  let sendTask ← async (t := AsyncTask) <| stream.send chunk
  let result ← stream.recv

  assert! result.isSome
  assert! result.get!.extensions.size == 1
  assert! result.get!.extensions[0]! == (Chunk.ExtensionName.mk "key", some <| .ofString! "value")
  await sendTask

#eval channelExtensions.block

-- Test incomplete sends are collapsed before delivery

def channelCollapseIncompleteChunks : Async Unit := do
  let stream ← Body.mkStream

  let first : Chunk := { data := "aaaaaaaaaa".toUTF8, extensions := #[(.mk "part", some <| .ofString! "first")] }
  let second : Chunk := { data := "bbbbbbbbbb".toUTF8, extensions := #[(.mk "part", some <| .ofString! "second")] }
  let last : Chunk := { data := "cccccccccccccccccccc".toUTF8, extensions := #[(.mk "part", some <| .ofString! "last")] }

  stream.send first (incomplete := true)
  stream.send second (incomplete := true)

  let noChunkYet ← stream.tryRecv
  assert! noChunkYet.isNone

  let sendFinal ← async (t := AsyncTask) <| stream.send last
  let result ← stream.recv

  assert! result.isSome
  let merged := result.get!
  assert! merged.data == "aaaaaaaaaabbbbbbbbbbcccccccccccccccccccc".toUTF8
  assert! merged.data.size == 40
  assert! merged.extensions == #[(.mk "part", some <| .ofString! "first")]

  await sendFinal

#eval channelCollapseIncompleteChunks.block

-- Test known size metadata

def channelKnownSize : Async Unit := do
  let stream ← Body.mkStream
  stream.setKnownSize (some (.fixed 100))
  let size ← stream.getKnownSize
  assert! size == some (.fixed 100)

#eval channelKnownSize.block

-- Test known size decreases when a chunk is consumed

def channelKnownSizeDecreases : Async Unit := do
  let stream ← Body.mkStream
  stream.setKnownSize (some (.fixed 5))

  let sendTask ← async (t := AsyncTask) <| stream.send (Chunk.ofByteArray "hello".toUTF8)
  let _ ← stream.recv
  await sendTask

  let size ← stream.getKnownSize
  assert! size == some (.fixed 0)

#eval channelKnownSizeDecreases.block

-- Test only one blocked producer is allowed

def channelSingleProducerRule : Async Unit := do
  let stream ← Body.mkStream
  let send1 ← async (t := AsyncTask) <| stream.send (Chunk.ofByteArray "one".toUTF8)

  -- Yield so `send1` can occupy the single pending-producer slot.
  let _ ← Selectable.one #[
    .case (← Selector.sleep 5) pure
  ]

  let send2Failed ←
    try
      stream.send (Chunk.ofByteArray "two".toUTF8)
      pure false
    catch _ =>
      pure true
  assert! send2Failed

  let first ← stream.recv
  assert! first.isSome
  assert! first.get!.data == "one".toUTF8

  await send1

#eval channelSingleProducerRule.block

-- Test only one blocked consumer is allowed

def channelSingleConsumerRule : Async Unit := do
  let stream ← Body.mkStream

  let recv1 ← async (t := AsyncTask) <| stream.recv

  let hasInterest ← Selectable.one #[
    .case stream.interestSelector pure
  ]
  assert! hasInterest

  let recv2Failed ←
    try
      let _ ← stream.recv
      pure false
    catch _ =>
      pure true

  assert! recv2Failed

  let sendTask ← async (t := AsyncTask) <| stream.send (Chunk.ofByteArray "ok".toUTF8)
  let r1 ← await recv1

  assert! r1.isSome
  assert! r1.get!.data == "ok".toUTF8
  await sendTask

#eval channelSingleConsumerRule.block

-- Test hasInterest reflects blocked receiver state

def channelHasInterest : Async Unit := do
  let stream ← Body.mkStream
  assert! !(← stream.hasInterest)

  let recvTask ← async (t := AsyncTask) <| stream.recv

  let hasInterest ← Selectable.one #[
    .case stream.interestSelector pure
  ]
  assert! hasInterest
  assert! (← stream.hasInterest)

  let sendTask ← async (t := AsyncTask) <| stream.send (Chunk.ofByteArray "x".toUTF8)
  let _ ← await recvTask
  await sendTask

  assert! !(← stream.hasInterest)

#eval channelHasInterest.block

-- Test interestSelector resolves false when stream closes first

def channelInterestSelectorClose : Async Unit := do
  let stream ← Body.mkStream

  let waitInterest ← async (t := AsyncTask) <|
    Selectable.one #[
      .case stream.interestSelector pure
    ]

  stream.close
  let interested ← await waitInterest
  assert! interested == false

#eval channelInterestSelectorClose.block

-- Test incomplete sends are buffered and merged into one chunk on the final send

def channelIncompleteChunks : Async Unit := do
  let stream ← Body.mkStream

  let sendTask ← async (t := AsyncTask) <| do
    stream.send (Chunk.ofByteArray "hel".toUTF8) (incomplete := true)
    stream.send (Chunk.ofByteArray "lo".toUTF8)

  let result ← stream.recv

  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8
  await sendTask

#eval channelIncompleteChunks.block

-- Test sending to a closed stream raises an error

def channelSendAfterClose : Async Unit := do
  let stream ← Body.mkStream
  stream.close

  let failed ←
    try
      stream.send (Chunk.ofByteArray "test".toUTF8)
      pure false
    catch _ =>
      pure true
  assert! failed

#eval channelSendAfterClose.block

-- Test Body.stream runs producer and returns the stream handle

def channelStreamHelper : Async Unit := do
  let stream ← Body.stream fun s => do
    s.send (Chunk.ofByteArray "hello".toUTF8)

  let result ← stream.recv
  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8

  let eof ← stream.recv
  assert! eof.isNone

#eval channelStreamHelper.block

-- Test Body.empty creates an already-closed Stream

def channelEmptyHelper : Async Unit := do
  let stream ← Body.empty
  assert! (← stream.isClosed)

  let result ← stream.recv
  assert! result.isNone

#eval channelEmptyHelper.block

-- Test Stream.readAll concatenates all chunks

def channelReadAll : Async Unit := do
  let stream ← Body.mkStream

  let sendTask ← async (t := AsyncTask) <| do
    stream.send (Chunk.ofByteArray "foo".toUTF8)
    stream.send (Chunk.ofByteArray "bar".toUTF8)
    stream.close

  let result : ByteArray ← stream.readAll
  assert! result == "foobar".toUTF8
  await sendTask

#eval channelReadAll.block

-- Test Stream.readAll enforces a maximum size limit

def channelReadAllMaxSize : Async Unit := do
  let stream ← Body.mkStream

  let sendTask ← async (t := AsyncTask) <| do
    stream.send (Chunk.ofByteArray "abcdefgh".toUTF8)
    stream.close

  let failed ←
    try
      let _ : ByteArray ← stream.readAll (maximumSize := some 4)
      pure false
    catch _ =>
      pure true
  assert! failed
  await sendTask

#eval channelReadAllMaxSize.block

-- Test Stream.getKnownSize reflects the value set via setKnownSize

def channelKnownSizeRoundtrip : Async Unit := do
  let stream ← Body.mkStream
  stream.setKnownSize (some (.fixed 42))

  let size ← stream.getKnownSize
  assert! size == some (.fixed 42)

#eval channelKnownSizeRoundtrip.block

/-! ## Full tests -/

-- Test Full.recv returns content once then EOF

def fullRecvConsumesOnce : Async Unit := do
  let full ← Body.Full.ofString "hello"
  let first ← full.recv
  let second ← full.recv

  assert! first.isSome
  assert! first.get!.data == "hello".toUTF8
  assert! second.isNone

#eval fullRecvConsumesOnce.block

-- Test Full known-size metadata tracks consumption

def fullKnownSizeLifecycle : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03, 0x04]
  let full ← Body.Full.ofByteArray data

  assert! (← full.getKnownSize) == some (.fixed 4)
  let chunk ← full.recv
  assert! chunk.isSome
  assert! chunk.get!.data == data
  assert! (← full.getKnownSize) == some (.fixed 0)

#eval fullKnownSizeLifecycle.block

-- Test Full.close discards remaining content

def fullClose : Async Unit := do
  let full ← Body.Full.ofString "bye"
  assert! !(← full.isClosed)
  full.close
  assert! (← full.isClosed)
  assert! (← full.recv).isNone

#eval fullClose.block

-- Test Full from an empty ByteArray returns none on the first recv

def fullEmptyBytes : Async Unit := do
  let full ← Body.Full.ofByteArray ByteArray.empty
  let result ← full.recv
  assert! result.isNone

#eval fullEmptyBytes.block

-- Test Full.recvSelector resolves immediately with the stored chunk

def fullRecvSelectorResolves : Async Unit := do
  let full ← Body.Full.ofString "world"
  let result ← Selectable.one #[
    .case full.recvSelector pure
  ]
  assert! result.isSome
  assert! result.get!.data == "world".toUTF8

#eval fullRecvSelectorResolves.block

-- Test Full.getKnownSize returns 0 after close

def fullKnownSizeAfterClose : Async Unit := do
  let full ← Body.Full.ofString "data"
  assert! (← full.getKnownSize) == some (.fixed 4)
  full.close
  assert! (← full.getKnownSize) == some (.fixed 0)

#eval fullKnownSizeAfterClose.block

-- Test Full.tryRecv succeeds once and returns none thereafter

def fullTryRecvIdempotent : Async Unit := do
  let full ← Body.Full.ofString "once"
  let first ← full.recv
  let second ← full.recv
  assert! first.isSome
  assert! first.get!.data == "once".toUTF8
  assert! second.isNone

#eval fullTryRecvIdempotent.block

/-! ## Empty tests -/

-- Test Empty.recv always returns none

def emptyBodyRecv : Async Unit := do
  let body : Body.Empty := {}
  let result ← body.recv
  assert! result.isNone

#eval emptyBodyRecv.block

-- Test Empty.isClosed is always true

def emptyBodyIsClosed : Async Unit := do
  let body : Body.Empty := {}
  assert! (← body.isClosed)

#eval emptyBodyIsClosed.block

-- Test Empty.close is a no-op: still closed and recv still returns none

def emptyBodyClose : Async Unit := do
  let body : Body.Empty := {}
  body.close
  assert! (← body.isClosed)
  let result ← body.recv
  assert! result.isNone

#eval emptyBodyClose.block

-- Test Empty.recvSelector resolves immediately with none

def emptyBodyRecvSelector : Async Unit := do
  let body : Body.Empty := {}
  let result ← Selectable.one #[
    .case body.recvSelector pure
  ]
  assert! result.isNone

#eval emptyBodyRecvSelector.block

/-! ## Any tests -/

-- Test Any wrapping a Full body forwards recv correctly

def anyFromFull : Async Unit := do
  let full ← Body.Full.ofString "hello"
  let any : Body.Any := full
  let result ← any.recv
  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8

#eval anyFromFull.block

-- Test Any wrapping an Empty body returns none and reports closed

def anyFromEmpty : Async Unit := do
  let empty : Body.Empty := {}
  let any : Body.Any := empty
  let result ← any.recv
  assert! result.isNone
  assert! (← any.isClosed)

#eval anyFromEmpty.block

-- Test Any wrapping an Incoming channel receives chunks

def anyFromChannel : Async Unit := do
  let outgoing ← Body.mkStream
  let any := Body.Any.ofBody outgoing

  let sendTask ← async (t := AsyncTask) <| outgoing.send (Chunk.ofByteArray "data".toUTF8)
  let result ← any.recv
  assert! result.isSome
  assert! result.get!.data == "data".toUTF8
  await sendTask

#eval anyFromChannel.block

-- Test Any.close closes the underlying body

def anyCloseForwards : Async Unit := do
  let full ← Body.Full.ofString "test"
  let any : Body.Any := full
  any.close
  assert! (← any.isClosed)
  let result ← any.recv
  assert! result.isNone

#eval anyCloseForwards.block

-- Test Any.recvSelector resolves immediately for a Full body

def anyRecvSelectorFromFull : Async Unit := do
  let full ← Body.Full.ofString "sel"
  let any : Body.Any := full
  let result ← Selectable.one #[
    .case any.recvSelector pure
  ]
  assert! result.isSome
  assert! result.get!.data == "sel".toUTF8

#eval anyRecvSelectorFromFull.block

/-! ## Request.Builder body tests -/

private def recvBuiltBody (body : Body.Full) : Async (Option Chunk) :=
  body.recv

-- Test Request.Builder.text sets correct headers

def requestBuilderText : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.text "Hello, World!"

  assert! req.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! req.line.headers.get? Header.Name.contentLength == none

  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval requestBuilderText.block

-- Test Request.Builder.json sets correct headers

def requestBuilderJson : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.json "{\"key\": \"value\"}"

  assert! req.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  assert! req.line.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "{\"key\": \"value\"}".toUTF8

#eval requestBuilderJson.block

-- Test Request.Builder.fromBytes sets body

def requestBuilderFromBytes : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03]
  let req ← Request.post (.originForm! "/api")
    |>.fromBytes data

  assert! req.line.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == data

#eval requestBuilderFromBytes.block

-- Test Request.Builder.noBody creates empty body

def requestBuilderNoBody : Async Unit := do
  let req ← Request.get (.originForm! "/api")
    |>.empty

  assert! req.body == {}

#eval requestBuilderNoBody.block

-- Test Request.Builder.bytes sets application/octet-stream content type

def requestBuilderBytes : Async Unit := do
  let data := ByteArray.mk #[0xde, 0xad, 0xbe, 0xef]
  let req ← Request.post (.originForm! "/api")
    |>.bytes data

  assert! req.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/octet-stream")
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == data

#eval requestBuilderBytes.block

-- Test Request.Builder.html sets text/html content type

def requestBuilderHtml : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.html "<h1>Hello</h1>"

  assert! req.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/html; charset=utf-8")
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "<h1>Hello</h1>".toUTF8

#eval requestBuilderHtml.block

-- Test Request.Builder.stream creates a streaming body

def requestBuilderStream : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.stream fun s => do
      s.send (Chunk.ofByteArray "streamed".toUTF8)

  let result ← req.body.recv
  assert! result.isSome
  assert! result.get!.data == "streamed".toUTF8

#eval requestBuilderStream.block

-- Test Request.Builder.noBody body is always closed and returns none

def requestBuilderNoBodyAlwaysClosed : Async Unit := do
  let req ← Request.get (.originForm! "/api")
    |>.empty

  assert! (← req.body.isClosed)
  let result ← req.body.recv
  assert! result.isNone

#eval requestBuilderNoBodyAlwaysClosed.block

/-! ## Response.Builder body tests -/

-- Test Response.Builder.text sets correct headers

def responseBuilderText : Async Unit := do
  let res ← Response.ok
    |>.text "Hello, World!"

  assert! res.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! res.line.headers.get? Header.Name.contentLength == none

  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval responseBuilderText.block

-- Test Response.Builder.json sets correct headers

def responseBuilderJson : Async Unit := do
  let res ← Response.ok
    |>.json "{\"status\": \"ok\"}"

  assert! res.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  assert! res.line.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "{\"status\": \"ok\"}".toUTF8

#eval responseBuilderJson.block

-- Test Response.Builder.fromBytes sets body

def responseBuilderFromBytes : Async Unit := do
  let data := ByteArray.mk #[0xaa, 0xbb]
  let res ← Response.ok
    |>.fromBytes data

  assert! res.line.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == data

#eval responseBuilderFromBytes.block

-- Test Response.Builder.noBody creates empty body

def responseBuilderNoBody : Async Unit := do
  let res ← Response.ok
    |>.empty

  assert! res.body == {}

#eval responseBuilderNoBody.block

-- Test Response.Builder.bytes sets application/octet-stream content type

def responseBuilderBytes : Async Unit := do
  let data := ByteArray.mk #[0xca, 0xfe]
  let res ← Response.ok
    |>.bytes data

  assert! res.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/octet-stream")
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == data

#eval responseBuilderBytes.block

-- Test Response.Builder.html sets text/html content type

def responseBuilderHtml : Async Unit := do
  let res ← Response.ok
    |>.html "<p>OK</p>"

  assert! res.line.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/html; charset=utf-8")
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "<p>OK</p>".toUTF8

#eval responseBuilderHtml.block

-- Test Response.Builder.stream creates a streaming body

def responseBuilderStream : Async Unit := do
  let res ← Response.ok
    |>.stream fun s => do
      s.send (Chunk.ofByteArray "streamed".toUTF8)

  let result ← res.body.recv
  assert! result.isSome
  assert! result.get!.data == "streamed".toUTF8

#eval responseBuilderStream.block

-- Test Response.Builder.noBody body is always closed and returns none

def responseBuilderNoBodyAlwaysClosed : Async Unit := do
  let res ← Response.ok
    |>.empty

  assert! (← res.body.isClosed)
  let result ← res.body.recv
  assert! result.isNone

#eval responseBuilderNoBodyAlwaysClosed.block

import Std.Internal.Http.Data.Body

open Std.Internal.IO Async
open Std.Http
open Std.Http.Body

/-! ## Channel tests -/

-- Test send and recv on channel

def channelSendRecv : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  let chunk := Chunk.ofByteArray "hello".toUTF8

  let sendTask ← async (t := AsyncTask) <| outgoing.send chunk
  let result ← incoming.recv none

  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8
  await sendTask

#eval channelSendRecv.block


-- Test tryRecv on empty channel returns none

def channelTryRecvEmpty : Async Unit := do
  let (_outgoing, incoming) ← Body.mkChannel
  let result ← incoming.tryRecv
  assert! result.isNone

#eval channelTryRecvEmpty.block

-- Test tryRecv consumes a waiting producer

def channelTryRecvWithPendingSend : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel

  let sendTask ← async (t := AsyncTask) <| outgoing.send (Chunk.ofByteArray "data".toUTF8)
  let mut result := none
  let mut fuel := 100
  while result.isNone && fuel > 0 do
    result ← incoming.tryRecv
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
  let (outgoing, incoming) ← Body.mkChannel
  assert! !(← outgoing.isClosed)
  outgoing.close
  assert! (← incoming.isClosed)

#eval channelClose.block

-- Test recv on closed channel returns none

def channelRecvAfterClose : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  outgoing.close
  let result ← incoming.recv none
  assert! result.isNone

#eval channelRecvAfterClose.block

-- Test Body.stream runs producer concurrently and transfers chunks

def bodyStreamSends : Async Unit := do
  let incoming ← Body.stream fun outgoing => do
    outgoing.send (Chunk.ofByteArray "x".toUTF8)

  let first ← incoming.recv none
  assert! first.isSome
  assert! first.get!.data == "x".toUTF8

  let done ← incoming.recv none
  assert! done.isNone

#eval bodyStreamSends.block

-- Test Body.stream closes channel when generator throws

def bodyStreamThrowCloses : Async Unit := do
  let incoming ← Body.stream fun _ => do
    throw (.userError "boom")

  let result ← incoming.recv none
  assert! result.isNone

#eval bodyStreamThrowCloses.block

-- Test for-in iteration collects chunks until close

def channelForIn : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel

  let producer ← async (t := AsyncTask) <| do
    outgoing.send (Chunk.ofByteArray "a".toUTF8)
    outgoing.send (Chunk.ofByteArray "b".toUTF8)
    outgoing.close

  let mut acc : ByteArray := .empty
  for chunk in incoming do
    acc := acc ++ chunk.data

  assert! acc == "ab".toUTF8
  await producer

#eval channelForIn.block

-- Test chunk extensions are preserved

def channelExtensions : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  let chunk := { data := "hello".toUTF8, extensions := #[(.mk "key", some "value")] : Chunk }

  let sendTask ← async (t := AsyncTask) <| outgoing.send chunk
  let result ← incoming.recv none

  assert! result.isSome
  assert! result.get!.extensions.size == 1
  assert! result.get!.extensions[0]! == (.mk "key", some "value")
  await sendTask

#eval channelExtensions.block

-- Test incomplete sends are collapsed before delivery

def channelCollapseIncompleteChunks : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel

  let first : Chunk := { data := "aaaaaaaaaa".toUTF8, extensions := #[(.mk "part", some "first")] }
  let second : Chunk := { data := "bbbbbbbbbb".toUTF8, extensions := #[(.mk "part", some "second")] }
  let last : Chunk := { data := "cccccccccccccccccccc".toUTF8, extensions := #[(.mk "part", some "last")] }

  outgoing.send first (incomplete := true)
  outgoing.send second (incomplete := true)

  let noChunkYet ← incoming.tryRecv
  assert! noChunkYet.isNone

  let sendFinal ← async (t := AsyncTask) <| outgoing.send last
  let result ← incoming.recv none

  assert! result.isSome
  let merged := result.get!
  assert! merged.data == "aaaaaaaaaabbbbbbbbbbcccccccccccccccccccc".toUTF8
  assert! merged.data.size == 40
  assert! merged.extensions == #[(.mk "part", some "first")]

  await sendFinal

#eval channelCollapseIncompleteChunks.block

-- Test known size metadata

def channelKnownSize : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  outgoing.setKnownSize (some (.fixed 100))
  let size ← incoming.getKnownSize
  assert! size == some (.fixed 100)

#eval channelKnownSize.block

-- Test known size decreases when a chunk is consumed

def channelKnownSizeDecreases : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  outgoing.setKnownSize (some (.fixed 5))

  let sendTask ← async (t := AsyncTask) <| outgoing.send (Chunk.ofByteArray "hello".toUTF8)
  let _ ← incoming.recv none
  await sendTask

  let size ← incoming.getKnownSize
  assert! size == some (.fixed 0)

#eval channelKnownSizeDecreases.block

-- Test only one blocked producer is allowed

def channelSingleProducerRule : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  let send1 ← async (t := AsyncTask) <| outgoing.send (Chunk.ofByteArray "one".toUTF8)

  -- Yield so `send1` can occupy the single pending-producer slot.
  let _ ← Selectable.one #[
    .case (← Selector.sleep 5) pure
  ]

  let send2Failed ←
    try
      outgoing.send (Chunk.ofByteArray "two".toUTF8)
      pure false
    catch _ =>
      pure true
  assert! send2Failed

  let first ← incoming.recv none
  assert! first.isSome
  assert! first.get!.data == "one".toUTF8

  await send1

#eval channelSingleProducerRule.block

-- Test only one blocked consumer is allowed

def channelSingleConsumerRule : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel

  let recv1 ← async (t := AsyncTask) <| incoming.recv none

  let hasInterest ← Selectable.one #[
    .case outgoing.interestSelector pure
  ]
  assert! hasInterest

  let recv2Failed ←
    try
      let _ ← incoming.recv none
      pure false
    catch _ =>
      pure true

  assert! recv2Failed

  let sendTask ← async (t := AsyncTask) <| outgoing.send (Chunk.ofByteArray "ok".toUTF8)
  let r1 ← await recv1

  assert! r1.isSome
  assert! r1.get!.data == "ok".toUTF8
  await sendTask

#eval channelSingleConsumerRule.block

-- Test hasInterest reflects blocked receiver state

def channelHasInterest : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel
  assert! !(← outgoing.hasInterest)

  let recvTask ← async (t := AsyncTask) <| incoming.recv none

  let hasInterest ← Selectable.one #[
    .case outgoing.interestSelector pure
  ]
  assert! hasInterest
  assert! (← outgoing.hasInterest)

  let sendTask ← async (t := AsyncTask) <| outgoing.send (Chunk.ofByteArray "x".toUTF8)
  let _ ← await recvTask
  await sendTask

  assert! !(← outgoing.hasInterest)

#eval channelHasInterest.block

-- Test interestSelector resolves false when channel closes first

def channelInterestSelectorClose : Async Unit := do
  let (outgoing, _incoming) ← Body.mkChannel

  let waitInterest ← async (t := AsyncTask) <|
    Selectable.one #[
      .case outgoing.interestSelector pure
    ]

  outgoing.close
  let interested ← await waitInterest
  assert! interested == false

#eval channelInterestSelectorClose.block

/-! ## Full tests -/

-- Test Full.recv returns content once then EOF

def fullRecvConsumesOnce : Async Unit := do
  let full ← Body.Full.ofUTF8String "hello"
  let first ← full.recv none
  let second ← full.recv none

  assert! first.isSome
  assert! first.get!.data == "hello".toUTF8
  assert! second.isNone

#eval fullRecvConsumesOnce.block

-- Test Full known-size metadata tracks consumption

def fullKnownSizeLifecycle : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03, 0x04]
  let full ← Body.Full.ofByteArray data

  assert! (← full.getKnownSize) == some (.fixed 4)
  let chunk ← full.tryRecv
  assert! chunk.isSome
  assert! chunk.get!.data == data
  assert! (← full.getKnownSize) == some (.fixed 0)

#eval fullKnownSizeLifecycle.block

-- Test Full.close discards remaining content

def fullClose : Async Unit := do
  let full ← Body.Full.ofUTF8String "bye"
  assert! !(← full.isClosed)
  full.close
  assert! (← full.isClosed)
  assert! (← full.tryRecv).isNone

#eval fullClose.block

-- Test Full interest API always reports no consumer interest

def fullInterest : Async Unit := do
  let full ← Body.Full.ofUTF8String "x"
  assert! !(← full.hasInterest)
  let interested ← Selectable.one #[
    .case full.interestSelector pure
  ]
  assert! interested == false

#eval fullInterest.block

/-! ## Empty tests -/

-- Test Empty writer metadata and interest behavior

def emptyWriterBasics : Async Unit := do
  let body : Body.Empty := {}
  assert! (← Writer.getKnownSize body) == some (.fixed 0)
  assert! !(← Writer.isClosed body)
  assert! !(← Writer.hasInterest body)

  Writer.setKnownSize body (some (.fixed 99))
  assert! (← Writer.getKnownSize body) == some (.fixed 0)

  Writer.close body
  let interested ← Selectable.one #[
    .case (Writer.interestSelector body) pure
  ]
  assert! interested == false

#eval emptyWriterBasics.block

-- Test Empty writer rejects send

def emptyWriterSendFails : Async Unit := do
  let body : Body.Empty := {}
  let failed ←
    try
      Writer.send body (Chunk.ofByteArray "x".toUTF8) false
      pure false
    catch _ =>
      pure true
  assert! failed

#eval emptyWriterSendFails.block

/-! ## Request.Builder body tests -/

private def recvBuiltBody (body : Body.Full) : Async (Option Chunk) :=
  body.recv none

private def emptyBodyKnownSize (body : Body.Empty) : Async (Option Body.Length) :=
  Writer.getKnownSize body

-- Test Request.Builder.text sets correct headers

def requestBuilderText : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.text "Hello, World!"

  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! req.head.headers.get? Header.Name.contentLength == none

  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval requestBuilderText.block

-- Test Request.Builder.json sets correct headers

def requestBuilderJson : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.json "{\"key\": \"value\"}"

  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  assert! req.head.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "{\"key\": \"value\"}".toUTF8

#eval requestBuilderJson.block

-- Test Request.Builder.fromBytes sets body

def requestBuilderFromBytes : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03]
  let req ← Request.post (.originForm! "/api")
    |>.fromBytes data

  assert! req.head.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == data

#eval requestBuilderFromBytes.block

-- Test Request.Builder.blank creates empty body

def requestBuilderNoBody : Async Unit := do
  let req ← Request.get (.originForm! "/api")
    |>.blank

  assert! (← emptyBodyKnownSize req.body) == some (.fixed 0)

#eval requestBuilderNoBody.block

/-! ## Response.Builder body tests -/

-- Test Response.Builder.text sets correct headers

def responseBuilderText : Async Unit := do
  let res ← Response.ok
    |>.text "Hello, World!"

  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! res.head.headers.get? Header.Name.contentLength == none

  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval responseBuilderText.block

-- Test Response.Builder.json sets correct headers

def responseBuilderJson : Async Unit := do
  let res ← Response.ok
    |>.json "{\"status\": \"ok\"}"

  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  assert! res.head.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "{\"status\": \"ok\"}".toUTF8

#eval responseBuilderJson.block

-- Test Response.Builder.fromBytes sets body

def responseBuilderFromBytes : Async Unit := do
  let data := ByteArray.mk #[0xaa, 0xbb]
  let res ← Response.ok
    |>.fromBytes data

  assert! res.head.headers.get? Header.Name.contentLength == none
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == data

#eval responseBuilderFromBytes.block

-- Test Response.Builder.blank creates empty body

def responseBuilderNoBody : Async Unit := do
  let res ← Response.ok
    |>.blank

  assert! (← emptyBodyKnownSize res.body) == some (.fixed 0)

#eval responseBuilderNoBody.block

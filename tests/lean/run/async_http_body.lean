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

-- Test sends are buffered when no consumer is waiting

def channelBufferedSends : Async Unit := do
  let (outgoing, incoming) ← Body.mkChannel

  outgoing.send (Chunk.ofByteArray "one".toUTF8)
  outgoing.send (Chunk.ofByteArray "two".toUTF8)

  let first ← incoming.recv none
  let second ← incoming.recv none

  assert! first.isSome
  assert! second.isSome
  assert! first.get!.data == "one".toUTF8
  assert! second.get!.data == "two".toUTF8

#eval channelBufferedSends.block

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
  let (outgoing, incoming) ← Body.mkChannel (capacity := 1)
  outgoing.send (Chunk.ofByteArray "one".toUTF8)

  let send2 ← async (t := AsyncTask) <| do
    try
      outgoing.send (Chunk.ofByteArray "two".toUTF8)
      return true
    catch _ =>
      return false

  -- Yield so `send2` can occupy the single blocked-producer slot.
  let _ ← Selectable.one #[
    .case (← Selector.sleep 5) pure
  ]

  let send3Failed ←
    try
      outgoing.send (Chunk.ofByteArray "three".toUTF8)
      pure false
    catch _ =>
      pure true
  assert! send3Failed

  let first ← incoming.recv none
  assert! first.isSome
  assert! first.get!.data == "one".toUTF8

  let ok2 ← await send2
  assert! ok2

  let second ← incoming.recv none
  assert! second.isSome
  assert! second.get!.data == "two".toUTF8

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

/-! ## Request.Builder body tests -/

private def recvBuiltBody (body : Body.Outgoing) : Async (Option Chunk) :=
  (Body.Internal.outgoingToIncoming body).recv none

private def tryRecvBuiltBody (body : Body.Outgoing) : Async (Option Chunk) :=
  (Body.Internal.outgoingToIncoming body).tryRecv

-- Test Request.Builder.text sets correct headers

def requestBuilderText : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.text "Hello, World!"

  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! req.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "13")

  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval requestBuilderText.block

-- Test Request.Builder.json sets correct headers

def requestBuilderJson : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.json "{\"key\": \"value\"}"

  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == "{\"key\": \"value\"}".toUTF8

#eval requestBuilderJson.block

-- Test Request.Builder.fromBytes sets content-length and body

def requestBuilderFromBytes : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03]
  let req ← Request.post (.originForm! "/api")
    |>.fromBytes data

  assert! req.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "3")
  let body ← recvBuiltBody req.body
  assert! body.isSome
  assert! body.get!.data == data

#eval requestBuilderFromBytes.block

-- Test Request.Builder.noBody creates empty body

def requestBuilderNoBody : Async Unit := do
  let req ← Request.get (.originForm! "/api")
    |>.noBody

  let body ← tryRecvBuiltBody req.body
  assert! body.isNone

#eval requestBuilderNoBody.block

/-! ## Response.Builder body tests -/

-- Test Response.Builder.text sets correct headers

def responseBuilderText : Async Unit := do
  let res ← Response.ok
    |>.text "Hello, World!"

  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! res.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "13")

  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval responseBuilderText.block

-- Test Response.Builder.json sets correct headers

def responseBuilderJson : Async Unit := do
  let res ← Response.ok
    |>.json "{\"status\": \"ok\"}"

  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == "{\"status\": \"ok\"}".toUTF8

#eval responseBuilderJson.block

-- Test Response.Builder.fromBytes sets content-length and body

def responseBuilderFromBytes : Async Unit := do
  let data := ByteArray.mk #[0xaa, 0xbb]
  let res ← Response.ok
    |>.fromBytes data

  assert! res.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "2")
  let body ← recvBuiltBody res.body
  assert! body.isSome
  assert! body.get!.data == data

#eval responseBuilderFromBytes.block

-- Test Response.Builder.noBody creates empty body

def responseBuilderNoBody : Async Unit := do
  let res ← Response.ok
    |>.noBody

  let body ← tryRecvBuiltBody res.body
  assert! body.isNone

#eval responseBuilderNoBody.block

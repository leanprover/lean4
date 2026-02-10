import Std.Internal.Http.Data.Body

open Std.Internal.IO Async
open Std.Http
open Std.Http.Body

/-! ## Stream tests -/

-- Test send followed by recv returns the chunk
def streamSendRecv : Async Unit := do
  let stream ← Stream.empty
  let chunk := Chunk.ofByteArray "hello".toUTF8
  stream.send chunk
  let result ← stream.recv none
  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8

#eval streamSendRecv.block

-- Test tryRecv on empty stream returns none
def streamTryRecvEmpty : Async Unit := do
  let stream ← Stream.empty
  let result ← stream.tryRecv
  assert! result.isNone

#eval streamTryRecvEmpty.block

-- Test tryRecv returns data when available
def streamTryRecvWithData : Async Unit := do
  let stream ← Stream.empty
  stream.send (Chunk.ofByteArray "data".toUTF8)
  let result ← stream.tryRecv
  assert! result.isSome
  assert! result.get!.data == "data".toUTF8

#eval streamTryRecvWithData.block

-- Test close sets the closed flag
def streamClose : Async Unit := do
  let stream ← Stream.empty
  assert! !(← stream.isClosed)
  stream.close
  assert! (← stream.isClosed)

#eval streamClose.block

-- Test recv on closed stream returns none
def streamRecvAfterClose : Async Unit := do
  let stream ← Stream.empty
  stream.close
  let result ← stream.recv none
  assert! result.isNone

#eval streamRecvAfterClose.block

-- Test FIFO ordering of multiple chunks
def streamMultipleFIFO : Async Unit := do
  let stream ← Stream.empty
  stream.send (Chunk.ofByteArray "one".toUTF8)
  stream.send (Chunk.ofByteArray "two".toUTF8)
  stream.send (Chunk.ofByteArray "three".toUTF8)
  let r1 ← stream.recv none
  let r2 ← stream.recv none
  let r3 ← stream.recv none
  assert! r1.get!.data == "one".toUTF8
  assert! r2.get!.data == "two".toUTF8
  assert! r3.get!.data == "three".toUTF8

#eval streamMultipleFIFO.block

-- Test for-in iteration collects all chunks until close
def streamForIn : Async Unit := do
  let stream ← Stream.empty
  stream.send (Chunk.ofByteArray "a".toUTF8)
  stream.send (Chunk.ofByteArray "b".toUTF8)
  stream.close

  let mut acc : ByteArray := .empty
  for chunk in stream do
    acc := acc ++ chunk.data
  assert! acc == "ab".toUTF8

#eval streamForIn.block

-- Test chunks preserve extensions
def streamExtensions : Async Unit := do
  let stream ← Stream.empty
  let chunk := { data := "hello".toUTF8, extensions := #[("key", some "value")] : Chunk }
  stream.send chunk
  let result ← stream.recv none
  assert! result.isSome
  assert! result.get!.extensions.size == 1
  assert! result.get!.extensions[0]! == ("key", some "value")

#eval streamExtensions.block

-- Test set/get known size
def streamKnownSize : Async Unit := do
  let stream ← Stream.empty
  stream.setKnownSize (some (.fixed 100))
  let size ← stream.getKnownSize
  assert! size == some (.fixed 100)

#eval streamKnownSize.block

-- Test capacity: filling up to capacity succeeds via tryRecv check
def streamCapacityFull : Async Unit := do
  let stream ← Stream.emptyWithCapacity (capacity := 3)
  stream.send (Chunk.ofByteArray "a".toUTF8)
  stream.send (Chunk.ofByteArray "b".toUTF8)
  stream.send (Chunk.ofByteArray "c".toUTF8)
  -- All three should be buffered
  let r1 ← stream.tryRecv
  let r2 ← stream.tryRecv
  let r3 ← stream.tryRecv
  let r4 ← stream.tryRecv
  assert! r1.get!.data == "a".toUTF8
  assert! r2.get!.data == "b".toUTF8
  assert! r3.get!.data == "c".toUTF8
  assert! r4.isNone

#eval streamCapacityFull.block

-- Test capacity: send blocks when buffer is full and resumes after recv
def streamCapacityBackpressure : Async Unit := do
  let stream ← Stream.emptyWithCapacity (capacity := 2)
  stream.send (Chunk.ofByteArray "a".toUTF8)
  stream.send (Chunk.ofByteArray "b".toUTF8)

  -- Spawn a send that should block because capacity is 2
  let sendTask ← async (t := AsyncTask) <|
    stream.send (Chunk.ofByteArray "c".toUTF8)

  -- Consume one to free space
  let r1 ← stream.recv none
  assert! r1.get!.data == "a".toUTF8

  -- Wait for the blocked send to complete
  sendTask.block

  -- Now we should be able to recv the remaining two
  let r2 ← stream.recv none
  let r3 ← stream.recv none
  assert! r2.get!.data == "b".toUTF8
  assert! r3.get!.data == "c".toUTF8

#eval streamCapacityBackpressure.block

-- Test capacity 1: only one chunk at a time
def streamCapacityOne : Async Unit := do
  let stream ← Stream.emptyWithCapacity (capacity := 1)
  stream.send (Chunk.ofByteArray "first".toUTF8)

  let sendTask ← async (t := AsyncTask) <|
    stream.send (Chunk.ofByteArray "second".toUTF8)

  let r1 ← stream.recv none
  assert! r1.get!.data == "first".toUTF8

  sendTask.block

  let r2 ← stream.recv none
  assert! r2.get!.data == "second".toUTF8

#eval streamCapacityOne.block

-- Test close unblocks pending producers
def streamCloseUnblocksProducers : Async Unit := do
  let stream ← Stream.emptyWithCapacity (capacity := 1)
  stream.send (Chunk.ofByteArray "fill".toUTF8)

  -- This send should block because buffer is full
  let sendTask ← async (t := AsyncTask) <|
    try
      stream.send (Chunk.ofByteArray "blocked".toUTF8)
    catch _ =>
      pure ()

  -- Close should unblock the producer (send gets error internally)
  stream.close

  await sendTask

#eval streamCloseUnblocksProducers.block

/-! ## Request.Builder body tests -/

-- Test Request.Builder.text sets correct headers
def requestBuilderText : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.text "Hello, World!"
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! req.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "13")
  let body ← req.body.tryRecv
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval requestBuilderText.block

-- Test Request.Builder.json sets correct headers
def requestBuilderJson : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.json "{\"key\": \"value\"}"
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  let body ← req.body.tryRecv
  assert! body.isSome
  assert! body.get!.data == "{\"key\": \"value\"}".toUTF8

#eval requestBuilderJson.block

-- Test Request.Builder.bytes sets correct headers
def requestBuilderBytes : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03]
  let req ← Request.post (.originForm! "/api")
    |>.bytes data
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/octet-stream")
  assert! req.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "3")
  let body ← req.body.tryRecv
  assert! body.isSome
  assert! body.get!.data == data

#eval requestBuilderBytes.block

-- Test Request.Builder.html sets correct headers
def requestBuilderHtml : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.html "<html></html>"
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/html; charset=utf-8")
  let body ← req.body.tryRecv
  assert! body.isSome

#eval requestBuilderHtml.block

-- Test Request.Builder.noBody creates empty body
def requestBuilderNoBody : Async Unit := do
  let req ← Request.get (.originForm! "/api")
    |>.noBody
  let body ← req.body.tryRecv
  assert! body.isNone

#eval requestBuilderNoBody.block

/-! ## Response.Builder body tests -/

-- Test Response.Builder.text sets correct headers
def responseBuilderText : Async Unit := do
  let res ← Response.ok
    |>.text "Hello, World!"
  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! res.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "13")
  let body ← res.body.tryRecv
  assert! body.isSome
  assert! body.get!.data == "Hello, World!".toUTF8

#eval responseBuilderText.block

-- Test Response.Builder.json sets correct headers
def responseBuilderJson : Async Unit := do
  let res ← Response.ok
    |>.json "{\"status\": \"ok\"}"
  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  let body ← res.body.tryRecv
  assert! body.isSome

#eval responseBuilderJson.block

-- Test Response.Builder.noBody creates empty body
def responseBuilderNoBody : Async Unit := do
  let res ← Response.ok
    |>.noBody
  let body ← res.body.tryRecv
  assert! body.isNone

#eval responseBuilderNoBody.block

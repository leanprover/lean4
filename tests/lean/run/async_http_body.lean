import Std.Internal.Http.Data.Body

open Std.Internal.IO Async
open Std.Http
open Std.Http.Body

/-! ## ChunkStream tests -/

-- Test send followed by recv returns the chunk
def chunkSendRecv : Async Unit := do
  let stream ← ChunkStream.empty
  let chunk := Chunk.ofByteArray "hello".toUTF8
  stream.send chunk
  let result ← stream.recv none
  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8

#eval chunkSendRecv.block

-- Test tryRecv on empty stream returns none
def chunkTryRecvEmpty : Async Unit := do
  let stream ← ChunkStream.empty
  let result ← stream.tryRecv
  assert! result.isNone

#eval chunkTryRecvEmpty.block

-- Test tryRecv returns data when available
def chunkTryRecvWithData : Async Unit := do
  let stream ← ChunkStream.empty
  stream.send (Chunk.ofByteArray "data".toUTF8)
  let result ← stream.tryRecv
  assert! result.isSome
  assert! result.get!.data == "data".toUTF8

#eval chunkTryRecvWithData.block

-- Test close sets the closed flag
def chunkClose : Async Unit := do
  let stream ← ChunkStream.empty
  assert! !(← stream.isClosed)
  stream.close
  assert! (← stream.isClosed)

#eval chunkClose.block

-- Test recv on closed stream returns none
def chunkRecvAfterClose : Async Unit := do
  let stream ← ChunkStream.empty
  stream.close
  let result ← stream.recv none
  assert! result.isNone

#eval chunkRecvAfterClose.block

-- Test FIFO ordering of multiple chunks
def chunkMultipleFIFO : Async Unit := do
  let stream ← ChunkStream.empty
  stream.send (Chunk.ofByteArray "one".toUTF8)
  stream.send (Chunk.ofByteArray "two".toUTF8)
  stream.send (Chunk.ofByteArray "three".toUTF8)
  let r1 ← stream.recv none
  let r2 ← stream.recv none
  let r3 ← stream.recv none
  assert! r1.get!.data == "one".toUTF8
  assert! r2.get!.data == "two".toUTF8
  assert! r3.get!.data == "three".toUTF8

#eval chunkMultipleFIFO.block

-- Test for-in iteration collects all chunks until close
def chunkForIn : Async Unit := do
  let stream ← ChunkStream.empty
  stream.send (Chunk.ofByteArray "a".toUTF8)
  stream.send (Chunk.ofByteArray "b".toUTF8)
  stream.close

  let mut acc : ByteArray := .empty
  for chunk in stream do
    acc := acc ++ chunk.data
  assert! acc == "ab".toUTF8

#eval chunkForIn.block

-- Test chunks preserve extensions
def chunkExtensions : Async Unit := do
  let stream ← ChunkStream.empty
  let chunk := { data := "hello".toUTF8, extensions := #[("key", some "value")] : Chunk }
  stream.send chunk
  let result ← stream.recv none
  assert! result.isSome
  assert! result.get!.extensions.size == 1
  assert! result.get!.extensions[0]! == ("key", some "value")

#eval chunkExtensions.block

-- Test set/get known size
def chunkKnownSize : Async Unit := do
  let stream ← ChunkStream.empty
  stream.setKnownSize (some (.fixed 100))
  let size ← stream.getKnownSize
  assert! size == some (.fixed 100)

#eval chunkKnownSize.block

-- Test capacity: filling up to capacity succeeds via tryRecv check
def chunkCapacityFull : Async Unit := do
  let stream ← ChunkStream.emptyWithCapacity (capacity := 3)
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

#eval chunkCapacityFull.block

-- Test capacity: send blocks when buffer is full and resumes after recv
def chunkCapacityBackpressure : Async Unit := do
  let stream ← ChunkStream.emptyWithCapacity (capacity := 2)
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

#eval chunkCapacityBackpressure.block

-- Test capacity 1: only one chunk at a time
def chunkCapacityOne : Async Unit := do
  let stream ← ChunkStream.emptyWithCapacity (capacity := 1)
  stream.send (Chunk.ofByteArray "first".toUTF8)

  let sendTask ← async (t := AsyncTask) <|
    stream.send (Chunk.ofByteArray "second".toUTF8)

  let r1 ← stream.recv none
  assert! r1.get!.data == "first".toUTF8

  sendTask.block

  let r2 ← stream.recv none
  assert! r2.get!.data == "second".toUTF8

#eval chunkCapacityOne.block

-- Test close unblocks pending producers
def chunkCloseUnblocksProducers : Async Unit := do
  let stream ← ChunkStream.emptyWithCapacity (capacity := 1)
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

#eval chunkCloseUnblocksProducers.block


/-! ## Full tests -/

-- Test ofData followed by recv
def fullOfData : Async Unit := do
  let full ← Full.new "hello".toUTF8
  let result ← full.recv none
  assert! result.isSome
  assert! result.get! == "hello".toUTF8

#eval fullOfData.block

-- Test data is consumed exactly once
def fullConsumedOnce : Async Unit := do
  let full ← Full.new "data".toUTF8
  let r1 ← full.recv none
  let r2 ← full.recv none
  assert! r1.isSome
  assert! r2.isNone

#eval fullConsumedOnce.block

-- Test empty Full returns none immediately
def fullEmpty : Async Unit := do
  let full ← Full.empty
  let result ← full.recv none
  assert! result.isNone

#eval fullEmpty.block

-- Test isClosed transitions after consumption
def fullClosedAfterConsume : Async Unit := do
  let full ← Full.new "data".toUTF8
  assert! !(← full.isClosed)
  discard <| full.recv none
  assert! (← full.isClosed)

#eval fullClosedAfterConsume.block

-- Test empty Full is already closed
def fullEmptyIsClosed : Async Unit := do
  let full ← Full.empty
  assert! (← full.isClosed)

#eval fullEmptyIsClosed.block

-- Test size? returns byte count
def fullSize : Async Unit := do
  let full ← Full.new "hello".toUTF8
  let size ← full.size?
  assert! size == some (.fixed 5)

#eval fullSize.block

-- Test size? returns none after consumption
def fullSizeAfterConsume : Async Unit := do
  let full ← Full.new "hello".toUTF8
  discard <| full.recv none
  let size ← full.size?
  assert! size == none

#eval fullSizeAfterConsume.block

-- Test send replaces data
def fullSendReplacesData : Async Unit := do
  let full ← Full.empty
  full.send "new data".toUTF8
  assert! !(← full.isClosed)
  let result ← full.recv none
  assert! result.isSome
  assert! result.get! == "new data".toUTF8

#eval fullSendReplacesData.block

-- Test recv? behaves the same as recv
def fullRecvQuestion : Async Unit := do
  let full ← Full.new "test".toUTF8
  let r1 ← full.recv?
  assert! r1.isSome
  assert! r1.get! == "test".toUTF8
  let r2 ← full.recv?
  assert! r2.isNone

#eval fullRecvQuestion.block

-- Test Full from String type
def fullFromString : Async Unit := do
  let full ← Full.new (β := String) "hello world"
  let result ← full.recv none
  assert! result.isSome
  assert! result.get! == "hello world".toUTF8

#eval fullFromString.block

/-! ## Body typeclass tests -/

-- Test Body instance for ChunkStream
def bodyChunkStream : Async Unit := do
  let stream : ChunkStream ← Body.empty
  Body.send stream (Chunk.ofByteArray "hello".toUTF8)
  let result ← Body.recv stream none
  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8
  assert! !(← Body.isClosed stream)

#eval bodyChunkStream.block

-- Test Body instance for Full
def bodyFull : Async Unit := do
  let full ← Full.new "hello".toUTF8
  let result ← @Body.recv Body.Full Chunk _ full none
  assert! result.isSome
  assert! result.get!.data == "hello".toUTF8
  assert! (← @Body.isClosed Body.Full Chunk _ full)

#eval bodyFull.block

/-! ## Empty body tests -/

-- Test Empty body recv returns none
def emptyRecv : Async Unit := do
  let empty ← Body.Empty.new
  let result ← empty.recv none
  assert! result.isNone

#eval emptyRecv.block

-- Test Empty body is always closed
def emptyIsClosed : Async Unit := do
  let empty ← Body.Empty.new
  assert! (← empty.isClosed)

#eval emptyIsClosed.block

-- Test Empty body size is 0
def emptySize : Async Unit := do
  let empty ← Body.Empty.new
  let size ← empty.size?
  assert! size == some (.fixed 0)

#eval emptySize.block

-- Test Body instance for Empty
def bodyEmpty : Async Unit := do
  let empty : Body.Empty ← Body.empty
  let result ← @Body.recv Body.Empty Chunk _ empty none
  assert! result.isNone
  assert! (← @Body.isClosed Body.Empty Chunk _ empty)

#eval bodyEmpty.block

/-! ## Request.Builder Full body tests -/

-- Test Request.Builder.text sets correct headers
def requestBuilderText : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.text "Hello, World!"
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! req.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "13")
  let body ← req.body.recv?
  assert! body.isSome
  assert! body.get! == "Hello, World!".toUTF8

#eval requestBuilderText.block

-- Test Request.Builder.json sets correct headers
def requestBuilderJson : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.json "{\"key\": \"value\"}"
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  let body ← req.body.recv?
  assert! body.isSome
  assert! body.get! == "{\"key\": \"value\"}".toUTF8

#eval requestBuilderJson.block

-- Test Request.Builder.bytes sets correct headers
def requestBuilderBytes : Async Unit := do
  let data := ByteArray.mk #[0x01, 0x02, 0x03]
  let req ← Request.post (.originForm! "/api")
    |>.bytes data
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/octet-stream")
  assert! req.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "3")
  let body ← req.body.recv?
  assert! body.isSome
  assert! body.get! == data

#eval requestBuilderBytes.block

-- Test Request.Builder.html sets correct headers
def requestBuilderHtml : Async Unit := do
  let req ← Request.post (.originForm! "/api")
    |>.html "<html></html>"
  assert! req.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/html; charset=utf-8")
  let body ← req.body.recv?
  assert! body.isSome

#eval requestBuilderHtml.block

-- Test Request.Builder.noBody creates empty body
def requestBuilderNoBody : Async Unit := do
  let req ← Request.get (.originForm! "/api")
    |>.noBody
  let body ← req.body.recv?
  assert! body.isNone

#eval requestBuilderNoBody.block

/-! ## Response.Builder Full body tests -/

-- Test Response.Builder.text sets correct headers
def responseBuilderText : Async Unit := do
  let res ← Response.ok
    |>.text "Hello, World!"
  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "text/plain; charset=utf-8")
  assert! res.head.headers.get? Header.Name.contentLength == some (Header.Value.ofString! "13")
  let body ← res.body.recv?
  assert! body.isSome
  assert! body.get! == "Hello, World!".toUTF8

#eval responseBuilderText.block

-- Test Response.Builder.json sets correct headers
def responseBuilderJson : Async Unit := do
  let res ← Response.ok
    |>.json "{\"status\": \"ok\"}"
  assert! res.head.headers.get? Header.Name.contentType == some (Header.Value.ofString! "application/json")
  let body ← res.body.recv?
  assert! body.isSome

#eval responseBuilderJson.block

-- Test Response.Builder.noBody creates empty body
def responseBuilderNoBody : Async Unit := do
  let res ← Response.ok
    |>.noBody
  let body ← res.body.recv?
  assert! body.isNone

#eval responseBuilderNoBody.block

import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

-- ============================================================================
-- collectByteArray tests
-- ============================================================================

def testCollectByteArrayExactMax : IO Unit := do
  let res ← Async.block do
    let data := ByteArray.mk (List.replicate 100 65 |>.toArray)
    let body := Body.bytes data
    let collected ← body.collectByteArray (some 100)
    return collected.size
  IO.println res

/--
info: 100
-/
#guard_msgs in
#eval testCollectByteArrayExactMax

def testCollectByteArrayOverLimit : IO Unit := do
  let res ← Async.block do
    let data := ByteArray.mk (List.replicate 101 65 |>.toArray)
    let body := Body.bytes data
    let _ ← body.collectByteArray (some 100)
    return "should not reach here"
  IO.println res

/--
error: body exceeds limit (100 bytes)
-/
#guard_msgs in
#eval testCollectByteArrayOverLimit

def testCollectByteArrayUnderLimit : IO Unit := do
  let res ← Async.block do
    let data := ByteArray.mk (List.replicate 50 65 |>.toArray)
    let body := Body.bytes data
    let collected ← body.collectByteArray (some 100)
    return collected.size
  IO.println res

/--
info: 50
-/
#guard_msgs in
#eval testCollectByteArrayUnderLimit

def testCollectByteArrayNoLimit : IO Unit := do
  let res ← Async.block do
    let data := ByteArray.mk (List.replicate 1000 65 |>.toArray)
    let body := Body.bytes data
    let collected ← body.collectByteArray none
    return collected.size
  IO.println res

/--
info: 1000
-/
#guard_msgs in
#eval testCollectByteArrayNoLimit

-- ============================================================================
-- collectString tests
-- ============================================================================

def testCollectStringValid : IO Unit := do
  let res ← Async.block do
    let body : Body := "hello"
    body.collectString none
  IO.println (repr res)

/--
info: some "hello"
-/
#guard_msgs in
#eval testCollectStringValid

def testCollectStringInvalidUtf8 : IO Unit := do
  let res ← Async.block do
    let invalidUtf8 := ByteArray.mk #[0xFF, 0xFE, 0x00, 0x01]
    let body := Body.bytes invalidUtf8
    body.collectString none
  IO.println (repr res)

/--
info: none
-/
#guard_msgs in
#eval testCollectStringInvalidUtf8

def testCollectStringEmpty : IO Unit := do
  let res ← Async.block do
    let body := Body.empty
    body.collectString none
  IO.println (repr res)

/--
info: some ""
-/
#guard_msgs in
#eval testCollectStringEmpty

-- ============================================================================
-- Streaming body tests
-- ============================================================================

def testStreamingBody : IO Unit := do
  let res ← Async.block do
    let stream ← Body.ByteStream.empty

    background do
      discard <| stream.write "hello ".toUTF8
      discard <| stream.write "world".toUTF8
      stream.close

    let body := Body.stream stream
    let result ← body.collectByteArray none
    return String.fromUTF8! result
  IO.println <| res.quote

/--
info: "hello world"
-/
#guard_msgs in
#eval testStreamingBody

def testStreamingMultipleChunks : IO Unit := do
  let count ← Async.block do
    let stream ← Body.ByteStream.empty

    background do
      for i in [0:3] do
        discard <| stream.write s!"chunk{i}".toUTF8
      stream.close

    let body := Body.stream stream
    let mut count := 0
    for _ in body do
      count := count + 1
    return count
  IO.println s!"collected {count} chunks"

/--
info: collected 3 chunks
-/
#guard_msgs in
#eval testStreamingMultipleChunks

def testStreamingTotalSize : IO Unit := do
  let size ← Async.block do
    let stream ← Body.ByteStream.empty

    background do
      discard <| stream.write "aaaaa".toUTF8
      discard <| stream.write "bbbbb".toUTF8
      discard <| stream.write "ccccc".toUTF8
      stream.close

    let body := Body.stream stream
    let collected ← body.collectByteArray none
    return collected.size
  IO.println size

/--
info: 15
-/
#guard_msgs in
#eval testStreamingTotalSize

-- ============================================================================
-- Empty body tests
-- ============================================================================

def testEmptyBodySize : IO Unit := do
  let size ← Async.block do
    let body := Body.empty
    let collected ← body.collectByteArray none
    return collected.size
  IO.println size

/--
info: 0
-/
#guard_msgs in
#eval testEmptyBodySize

def testEmptyBodyLength : IO Unit := do
  let isZero ← Async.block do
    let body := Body.empty
    let len ← body.getContentLength
    return (len == .fixed 0)
  IO.println isZero

/--
info: true
-/
#guard_msgs in
#eval testEmptyBodyLength

-- ============================================================================
-- Content length tests
-- ============================================================================

def testContentLengthFixed : IO Unit := do
  let len ← Async.block do
    let body : Body := "hello"
    body.getContentLength
  IO.println (repr len)

/--
info: Std.Http.Body.Length.fixed 5
-/
#guard_msgs in
#eval testContentLengthFixed

def testContentLengthEmpty : IO Unit := do
  let len ← Async.block do
    let body := Body.empty
    body.getContentLength
  IO.println (repr len)

/--
info: Std.Http.Body.Length.fixed 0
-/
#guard_msgs in
#eval testContentLengthEmpty

-- ============================================================================
-- Body coercions
-- ============================================================================

def testStringCoercion : IO Unit := do
  let size ← Async.block do
    let body : Body := "hello"
    let collected ← body.collectByteArray none
    return collected.size
  IO.println size

/--
info: 5
-/
#guard_msgs in
#eval testStringCoercion

def testByteArrayCoercion : IO Unit := do
  let size ← Async.block do
    let data := ByteArray.mk #[1, 2, 3]
    let body : Body := data
    let collected ← body.collectByteArray none
    return collected.size
  IO.println size

/--
info: 3
-/
#guard_msgs in
#eval testByteArrayCoercion

def testUnitCoercion : IO Unit := do
  let size ← Async.block do
    let body : Body := ()
    let collected ← body.collectByteArray none
    return collected.size
  IO.println size

/--
info: 0
-/
#guard_msgs in
#eval testUnitCoercion

-- ============================================================================
-- Body iteration
-- ============================================================================

def testBytesBodyIteration : IO Unit := do
  let count ← Async.block do
    let body : Body := "hello"
    let mut count := 0
    for _ in body do
      count := count + 1
    return count
  IO.println count

/--
info: 1
-/
#guard_msgs in
#eval testBytesBodyIteration

def testEmptyBodyIteration : IO Unit := do
  let count ← Async.block do
    let body := Body.empty
    let mut count := 0
    for _ in body do
      count := count + 1
    return count
  IO.println count

/--
info: 0
-/
#guard_msgs in
#eval testEmptyBodyIteration

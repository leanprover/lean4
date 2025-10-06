import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

-- Test basic message reception from multiple channels
def testSimpleMessages : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)
  let channelC ← Std.Channel.new (α := Nat)

  let channel := Std.StreamMap.ofArray #[
    ("a", channelA),
    ("b", channelB),
    ("c", channelC),
  ]

  await (← channelC.send 1)
  let (name, message) ← channel.recv
  assert! name == "c" && message == 1

  await (← channelA.send 2)
  let (name, message) ← channel.recv
  assert! name == "a" && message == 2

  await (← channelB.send 3)
  let (name, message) ← channel.recv
  assert! name == "b" && message == 3

#eval testSimpleMessages.block

-- Test empty StreamMap
def testEmpty : Async Unit := do
  let stream : Std.StreamMap String Nat := Std.StreamMap.empty

  assert! stream.isEmpty
  assert! stream.size == 0
  assert! stream.keys.size == 0

#eval testEmpty.block

-- Test register and unregister operations
def testRegisterUnregister : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.empty.register "a" channelA

  assert! stream.contains "a"
  assert! not (stream.contains "b")
  assert! stream.size == 1

  let stream := stream.register "b" channelB
  assert! stream.contains "a" && stream.contains "b"
  assert! stream.size == 2

  let stream := stream.unregister "a"
  assert! not (stream.contains "a")
  assert! stream.contains "b"
  assert! stream.size == 1

  let stream := stream.unregister "b"
  assert! stream.isEmpty

#eval testRegisterUnregister.block

-- Test replacing existing stream with same name
def testRegisterReplace : Async Unit := do
  let channelA1 ← Std.Channel.new (α := Nat)
  let channelA2 ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.empty.register "a" channelA1
  assert! stream.size == 1

  -- Register with same name should replace
  let stream := stream.register "a" channelA2
  assert! stream.size == 1
  assert! stream.contains "a"

  -- Send to new channel
  await (← channelA2.send 42)
  let (name, message) ← stream.recv
  assert! name == "a" && message == 42

#eval testRegisterReplace.block

-- Test keys functionality
def testKeys : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)
  let channelC ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("c", .mk channelC),
    ("a", .mk channelA),
    ("b", .mk channelB),
  ]

  let keys := stream.keys
  assert! keys.size == 3
  assert! keys.contains "a"
  assert! keys.contains "b"
  assert! keys.contains "c"

#eval testKeys.block

-- Test get? functionality
def testGet : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("a", .mk channelA),
    ("b", .mk channelB),
  ]

  let selectorA := stream.get? "a"
  let selectorC := stream.get? "c"

  assert! selectorA.isSome
  assert! selectorC.isNone

#eval testGet.block

-- Test filterByName functionality
def testFilterByName : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)
  let channelC ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("prefix_a", .mk channelA),
    ("prefix_b", .mk channelB),
    ("other_c", .mk channelC),
  ]

  let filtered := stream.filterByName (fun name => name.startsWith "prefix_")

  assert! filtered.size == 2
  assert! filtered.contains "prefix_a"
  assert! filtered.contains "prefix_b"
  assert! not (filtered.contains "other_c")

#eval testFilterByName.block

-- Test toArray functionality
def testToArray : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("a", .mk channelA),
    ("b", .mk channelB),
  ]

  let array := stream.toArray
  assert! array.size == 2

  let names := array.map (·.1)
  assert! names.contains "a"
  assert! names.contains "b"

#eval testToArray.block

-- Test multiple messages from same channel
def testMultipleFromSame : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("a", .mk channelA),
    ("b", .mk channelB),
  ]

  -- Send multiple messages to same channel
  await (← channelA.send 1)
  await (← channelA.send 2)
  await (← channelB.send 10)

  let (name1, msg1) ← stream.recv
  let (name2, msg2) ← stream.recv
  let (name3, msg3) ← stream.recv

  -- Should receive all messages, order may vary but names should match sources
  assert! (name1 == "a" && msg1 == 1) || (name1 == "a" && msg1 == 2) || (name1 == "b" && msg1 == 10)
  assert! (name2 == "a" && msg2 == 1) || (name2 == "a" && msg2 == 2) || (name2 == "b" && msg2 == 10)
  assert! (name3 == "a" && msg3 == 1) || (name3 == "a" && msg3 == 2) || (name3 == "b" && msg3 == 10)

#eval testMultipleFromSame.block

-- Test interleaved messages from different channels
def testInterleavedMessages : Async Unit := do
  let channelA ← Std.Channel.new (α := String)
  let channelB ← Std.Channel.new (α := String)
  let channelC ← Std.Channel.new (α := String)

  let stream := Std.StreamMap.ofArray #[
    ("first", .mk channelA),
    ("second", .mk channelB),
    ("third", .mk channelC),
  ]

  -- Send messages in specific order
  await (← channelB.send "msg1")
  await (← channelA.send "msg2")
  await (← channelC.send "msg3")
  await (← channelA.send "msg4")

  let results ← (List.range 4).mapM (fun _ => stream.recv)

  -- Verify we got all messages (order may vary)
  let messages := results.map (·.2)
  assert! messages.contains "msg1"
  assert! messages.contains "msg2"
  assert! messages.contains "msg3"
  assert! messages.contains "msg4"

#eval testInterleavedMessages.block

-- Test with different data typez
def testDifferentTypes : Async Unit := do
  let channelStr ← Std.Channel.new (α := String)
  let channelBool ← Std.Channel.new (α := String)

  let stream := Std.StreamMap.ofArray #[
    ("strings", .mk channelStr),
    ("bools", .mk channelBool),
  ]

  await (← channelStr.send "hello")
  await (← channelBool.send "world")

  let (name1, msg1) ← stream.recv
  let (name2, msg2) ← stream.recv

  assert! ((name1 == "strings" && msg1 == "hello") || (name1 == "bools" && msg1 == "world"))
  assert! ((name2 == "strings" && msg2 == "hello") || (name2 == "bools" && msg2 == "world"))
  assert! name1 != name2

#eval testDifferentTypes.block

-- Test unregister during operation
def testUnregisterDuringOperation : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)
  let channelC ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("a", .mk channelA),
    ("b", .mk channelB),
    ("c", .mk channelC),
  ]

  await (← channelA.send 1)
  await (← channelB.send 2)
  await (← channelC.send 3)

  assert! (← stream.tryRecv).isSome
  assert! (← stream.tryRecv).isSome
  assert! (← stream.tryRecv).isSome

  let stream := stream.unregister "b"
  assert! not (stream.contains "b")
  assert! stream.size == 2

  let newChannelD ← Std.Channel.new (α := Nat)
  let stream := stream.register "d" newChannelD

  await (← newChannelD.send 4)
  let (name2, msg2) ← stream.recv

  assert! name2 == "d" && msg2 == 4

#eval testUnregisterDuringOperation.block

-- Test selector functionality
def testSelector : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("a", .mk channelA),
    ("b", .mk channelB),
  ]

  let selector ← stream.selector

  await (← channelA.send 42)

  let result ← Selectable.one #[.case selector (fun x => pure x)]
  assert! result.1 == "a" && result.2 == 42

#eval testSelector.block

def testClose : Async Unit := do
  let channelA ← Std.Channel.new (α := Nat)
  let channelB ← Std.Channel.new (α := Nat)

  let stream := Std.StreamMap.ofArray #[
    ("a", .mk channelA),
    ("b", .mk channelB),
  ]

  stream.close

#eval testClose.block

-- Test large number of channels
def testManyChannels : Async Unit := do
  let channels : Vector _ 128 ← Vector.ofFnM (fun _ => Std.Channel.new (α := Nat))

  let streamArray := channels.mapIdx (fun i ch => (s!"channel_{i}", .mk ch))
  let stream := Std.StreamMap.ofArray streamArray.toArray

  assert! stream.size == 128

  await (← channels[3].send 100)
  await (← channels[7].send 200)

  let (name1, msg1) ← stream.recv
  let (name2, msg2) ← stream.recv

  assert! ((name1 == "channel_3" && msg1 == 100) || (name1 == "channel_7" && msg1 == 200))
  assert! ((name2 == "channel_3" && msg2 == 100) || (name2 == "channel_7" && msg2 == 200))
  assert! name1 != name2

#eval testManyChannels.block

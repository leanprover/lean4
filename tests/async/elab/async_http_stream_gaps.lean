import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests that a streamed response may pause between chunks longer than `Config.lingeringTimeout`.
Waiting for the handler's next chunk is not waiting for the client, so the connection keeps the
response going and ends it with its last chunk; a write that stalls is `writeTimeout`'s.
-/

#eval runGroup "streamed response with gaps" do
  checkTimed "gaps longer than lingeringTimeout" (ms := 5000) (raw := mkGetClose "/")
    (handler := fun _ =>
      Response.ok |>.stream fun s => do
        for c in ["a", "b", "c"] do
          s.send (Chunk.ofByteArray c.toUTF8)
          sleep 300)
    (expect := fun r => do
      assertStatus r "HTTP/1.1 200"
      assertContains r "1\x0d\na\x0d\n1\x0d\nb\x0d\n1\x0d\nc\x0d\n0\x0d\n\x0d\n")
    (config := { defaultConfig with lingeringTimeout := 100 })

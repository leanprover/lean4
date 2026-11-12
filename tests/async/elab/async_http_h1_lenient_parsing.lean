import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test

/-!
Tests request syntax that HTTP/1.1 allows and the server must accept: empty lines before a request
line, also right before EOF (RFC 9112 §2.2); obs-text in a quoted chunk-extension value (RFC 9112
§7.1.1, RFC 9110 §5.6.4); and leading zeros in a chunk size (`chunk-size = 1*HEXDIG`, RFC 9112 §7.1).
-/

#eval runGroup "empty lines before EOF" do
  checkClose "CRLF after a body, then EOF"
    "POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: 2\x0d\n\x0d\nhi\x0d\n" okHandler fun r => do
      assertStatus r "HTTP/1.1 200"
      assertResponseCount r 1
  checkClose "only empty lines, then EOF" "\x0d\n\x0d\n" okHandler fun r =>
    assertExact r ""

#eval runGroup "obs-text in a quoted chunk extension" do
  for ext in [";n=\"é\"", ";n=\"a\\é\"", ";a=1;n=\"é\";b"] do
    checkClose s!"extension {ext.quote}" (mkChunked "/" s!"5{ext}\x0d\nhello\x0d\n0\x0d\n\x0d\n") echoHandler
      fun r => do
        assertStatus r "HTTP/1.1 200"
        assertContains r "\x0d\n\x0d\nhello"

#eval runGroup "leading zeros in a chunk size" do
  for size in ["00000000000000005", String.join (List.replicate 40 "0") ++ "5"] do
    checkClose s!"chunk size {size}" (mkChunked "/" s!"{size}\x0d\nhello\x0d\n0\x0d\n\x0d\n") echoHandler
      fun r => do
        assertStatus r "HTTP/1.1 200"
        assertContains r "\x0d\n\x0d\nhello"
  -- Control: 17 significant digits are still too large.
  checkClose "chunk size 10000000000000000" (mkChunked "/" "10000000000000000\x0d\nhello\x0d\n") echoHandler
    fun r => assertStatus r "HTTP/1.1 400"

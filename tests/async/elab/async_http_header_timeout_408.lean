import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests the answer to a request head that stops arriving (`Config.headerTimeout`). Once part of a head
arrived, the server answers `408 Request Timeout` with `Connection: close` and closes (RFC 9110
§15.5.9), whether the head stopped in the request line, in a field line or before the empty line that
ends it, also after an earlier request on the same connection. Empty lines alone close the
connection silently, as an idle keep-alive connection does.
-/

def config : Config := { defaultConfig with headerTimeout := 200 }

#eval runGroup "header timeout" do
  checkTimed "in the request line" (raw := "GET / HT") (handler := okHandler)
    (expect := fun r => assertExact r r408) (config := config)
  checkTimed "in a field line" (raw := "GET / HTTP/1.1\x0d\nHo") (handler := okHandler)
    (expect := fun r => assertExact r r408) (config := config)
  checkTimed "before the end of the head" (raw := "GET / HTTP/1.1\x0d\nHost: a\x0d\n")
    (handler := okHandler) (expect := fun r => assertExact r r408) (config := config)
  checkTimed "after a request" (raw := mkGet "/a" ++ "GET /b HTTP/1.1\x0d\nHo") (handler := okHandler)
    (expect := fun r => do
      assertStatus r "HTTP/1.1 200"
      assertContains r r408
      assertResponseCount r 2)
    (config := config)
  checkTimed "only empty lines" (raw := "\x0d\n\x0d\n") (handler := okHandler)
    (expect := fun r => assertExact r "") (config := config)

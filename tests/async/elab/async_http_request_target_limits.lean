import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test

/-!
Tests the limits on request-targets and URIs. A target is bounded as a whole by `maxUriLength`, and a
target refused as too long gets `414`, never `400` (RFC 9112 §3), whatever its segments, segment
count or query parameters. `URI.parse?`, which `decideRedirect` uses on `Location`, has no
per-component limit tighter than the whole URI's.
-/

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

#eval runGroup "valid targets under maxUriLength" do
  for (label, target) in [
      ("257-byte segment", "/" ++ repeatStr "a" 257),
      ("600-byte segment", "/" ++ repeatStr "a" 600),
      ("129 segments", repeatStr "/a" 129),
      ("101 query parameters", "/?" ++ "&".intercalate (List.replicate 101 "a=1"))] do
    check label (mkGetClose target) uriHandler fun r => assertStatus r "HTTP/1.1 200"

-- The status code grows monotonically with the target's length: 200 up to the limit, 414 beyond it.
#eval runGroup "start-line limit" do
  -- `GET ` and ` HTTP/1.1\r\n` add 15 bytes, so a 8177-byte target makes a 8192-byte line.
  check "8177-byte target" (mkGetClose ("/" ++ repeatStr "a" 8176)) uriHandler fun r =>
    assertStatus r "HTTP/1.1 200"
  for length in [8178, 8192, 8193] do
    check s!"{length}-byte target" (mkGetClose ("/" ++ repeatStr "a" (length - 1))) uriHandler fun r =>
      assertStatus r "HTTP/1.1 414"

-- A small `maxUriLength` still answers 414.
#eval runGroup "configured maxUriLength" do
  check "400-byte target, maxUriLength 300" (mkGetClose ("/" ++ repeatStr "a" 399)) uriHandler
    (fun r => assertStatus r "HTTP/1.1 414")
    (config := { defaultConfig with maxUriLength := 300 })

-- `URI.parse?` accepts what a `Location` field may carry.
#eval show IO Unit from do
  for (label, uri) in [
      ("257-byte segment", "http://example.com/" ++ repeatStr "a" 257),
      ("129 segments", "http://example.com" ++ repeatStr "/a" 129),
      ("101 query parameters", "http://example.com/?" ++ "&".intercalate (List.replicate 101 "a=1")),
      ("1100-byte fragment", "http://example.com/#" ++ repeatStr "f" 1100),
      ("16-character scheme", "chrome-extension://abcdef/x")] do
    expect (URI.parse? uri).isSome s!"URI.parse? rejected a URI with a {label}"

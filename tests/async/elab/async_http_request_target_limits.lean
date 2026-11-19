import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test

/-!
Tests the limits on request-targets and URIs. A target is bounded as a whole by `maxUriLength`, and a
target refused as too long gets `414`, never `400` (RFC 9112 §3), whatever its segments, segment
count or query parameters. `maxPathSegments` and `maxQueryParams` (#16523) bound the element counts,
empty elements included, and a target over either also gets `414`. `URI.parse?`, which
`decideRedirect` uses on `Location`, has no per-component limit tighter than the whole URI's.
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

-- #16523: element counts at the limit pass, one more gets 414. Empty segments and parameters count.
#eval runGroup "configured maxPathSegments" do
  let config := { defaultConfig with maxPathSegments := some 8 }
  for (label, target, status) in [
      ("8 segments", repeatStr "/a" 8, "200"),
      ("9 segments", repeatStr "/a" 9, "414"),
      ("8 empty segments", repeatStr "/" 8, "200"),
      ("9 empty segments", repeatStr "/" 9, "414"),
      ("9 segments, absolute-form", "http://example.com" ++ repeatStr "/a" 9, "414"),
      ("9 segments, query parameters unlimited", repeatStr "/a" 9 ++ "?a=1", "414")] do
    check label (mkGetClose target) uriHandler (fun r => assertStatus r s!"HTTP/1.1 {status}")
      (config := config)

#eval runGroup "configured maxQueryParams" do
  let config := { defaultConfig with maxQueryParams := some 8 }
  for (label, target, status) in [
      ("8 parameters", "/?" ++ "&".intercalate (List.replicate 8 "a=1"), "200"),
      ("9 parameters", "/?" ++ "&".intercalate (List.replicate 9 "a=1"), "414"),
      ("8 empty parameters", "/?" ++ repeatStr "&" 7, "200"),
      ("9 empty parameters", "/?" ++ repeatStr "&" 8, "414"),
      ("9 parameters, absolute-form", "http://example.com/?" ++ repeatStr "&" 8, "414"),
      ("empty query", "/?", "200"),
      ("many segments, path segments unlimited", repeatStr "/a" 100 ++ "?a=1", "200")] do
    check label (mkGetClose target) uriHandler (fun r => assertStatus r s!"HTTP/1.1 {status}")
      (config := config)

-- With neither set, only `maxUriLength` bounds the counts: one element per byte is accepted.
#eval runGroup "unset element limits" do
  check "8000 empty parameters" (mkGetClose ("/?" ++ repeatStr "&" 7999)) uriHandler
    fun r => assertStatus r "HTTP/1.1 200"
  check "8000 empty segments" (mkGetClose (repeatStr "/" 8000)) uriHandler
    fun r => assertStatus r "HTTP/1.1 200"

-- `URI.parse?` accepts what a `Location` field may carry.
#eval show IO Unit from do
  for (label, uri) in [
      ("257-byte segment", "http://example.com/" ++ repeatStr "a" 257),
      ("129 segments", "http://example.com" ++ repeatStr "/a" 129),
      ("101 query parameters", "http://example.com/?" ++ "&".intercalate (List.replicate 101 "a=1")),
      ("1100-byte fragment", "http://example.com/#" ++ repeatStr "f" 1100),
      ("16-character scheme", "chrome-extension://abcdef/x")] do
    expect (URI.parse? uri).isSome s!"URI.parse? rejected a URI with a {label}"

import Std.Http.Protocol.H1

open Std.Http
open Std.Http.Protocol.H1

/-!
Regression test: `decideRedirect` treats a 3xx status it does not recognize as `300 Multiple Choices`
(RFC 9110 §15: a client MUST treat an unrecognized status code as the x00 code of its class), and so
does not follow it, as it does not follow 300 (RFC 9110 §15.4.1). The five redirect codes are still
followed.
-/

private def base : URI := URI.parse! "http://example.com/a/b"

private def origin : URI.Origin :=
  { scheme := base.scheme, host := base.host?.get!, port := base.port }

private def mkReq (method : Method) : Request.Head :=
  { method, version := .v11, uri := base.originTarget,
    headers := Headers.empty.insert .host (Header.Value.ofString! "example.com") }

private def withLocation (loc : String) : Headers :=
  Headers.empty.insert .location (Header.Value.ofString! loc)

private def isDone : RedirectOutcome → Bool
  | .done => true
  | .follow _ => false

private def code (n : UInt16) : Status := (Status.ofCode none n).get!

-- Unrecognized 3xx codes, for safe and unsafe methods, same-origin and cross-origin `Location`s.
#guard [309, 310, 333, 350, 399].all fun n =>
  [Method.get, .head, .post, .put, .delete].all fun m =>
    ["/x", "http://other.com/x", "//other.com/x", "?q"].all fun loc =>
      isDone (decideRedirect origin (mkReq m) true (code n) (withLocation loc))

-- 300 and the other codes that are never followed stay terminal.
#guard [300, 304, 305, 306].all fun n =>
  isDone (decideRedirect origin (mkReq .get) true (code n) (withLocation "/x"))

-- The five redirect codes are still followed.
#guard [301, 302, 303, 307, 308].all fun n =>
  !isDone (decideRedirect origin (mkReq .get) true (code n) (withLocation "/x"))

import Std.Http

open Std.Async
open Std Http

/-!
Tests the body and URI helpers an HTTP client builds on: `Body.Stream.trySend`, which hands a chunk
only to a receiver already waiting and keeps nothing otherwise; `Body.Stream.closedSelector`, which
fires when the stream closes but not when a receiver waits; `URI.origin?`, `URI.toOriginRequest?`
and the RFC 6454 serialization of `URI.Origin`; and the identity coercion `Body.Any → Body.Any`.
-/

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def chunk (s : String) : Chunk := Chunk.ofByteArray s.toUTF8

/-- Waits until a receiver is blocked on `s`. -/
def untilInterest (s : Body.Stream) : Async Unit := do
  repeat
    if ← s.hasInterest then break
    sleep 1

-- `trySend`
#eval show IO Unit from Async.block do
  -- Nobody waits: the chunk is refused and not kept.
  let s ← Body.mkStream
  expect (!(← s.trySend (chunk "a"))) "trySend with no receiver returned true"
  expect ((← s.tryRecv).isNone) "trySend kept a chunk nobody took"

  -- A waiting receiver gets it, and a known size counts it.
  let s ← Body.mkStream
  s.setKnownSize (some (.fixed 5))
  let got ← async s.recv
  untilInterest s
  expect (← s.trySend (chunk "abc")) "trySend to a waiting receiver returned false"
  expect (((← await got).map (String.fromUTF8! ·.data)) == some "abc") "receiver got the wrong chunk"
  expect ((← s.getKnownSize) == some (.fixed 2)) "known size not decreased"

  -- Incomplete pieces are buffered as with `send`, and join the next complete chunk.
  let s ← Body.mkStream
  expect (← s.trySend (chunk "ab") (incomplete := true)) "incomplete trySend returned false"
  let got ← async s.recv
  untilInterest s
  expect (← s.trySend (chunk "cd")) "trySend after pieces returned false"
  expect (((← await got).map (String.fromUTF8! ·.data)) == some "abcd") "pieces not joined"

  -- A closed stream refuses it with an error.
  let s ← Body.mkStream
  s.close
  let failed ← try discard (s.trySend (chunk "a")); pure false catch _ => pure true
  expect failed "trySend on a closed stream did not throw"

-- `closedSelector`
#eval show IO Unit from Async.block do
  let closedOrTimeout (s : Body.Stream) (ms : Nat) : Async Bool := do
    Selectable.one #[
      .case s.closedSelector (fun _ => pure true),
      .case (← Selector.sleep (.ofNat ms)) (fun _ => pure false)]

  -- An open stream with a waiting receiver does not fire it.
  let s ← Body.mkStream
  let _ ← async s.recv
  untilInterest s
  expect (!(← closedOrTimeout s 50)) "closedSelector fired on an open stream"

  -- Closing fires it, cleanly or with an error, and an already closed stream fires it at once.
  for withError in [false, true] do
    let s ← Body.mkStream
    let waiting ← async (closedOrTimeout s 2000)
    sleep 20
    if withError then s.closeWithError (.userError "boom") else s.close
    expect (← await waiting) s!"closedSelector did not fire on close (error: {withError})"
    expect (← closedOrTimeout s 2000) "closedSelector did not fire on a closed stream"

-- `URI.origin?`, `URI.toOriginRequest?` and `ToString URI.Origin`
#eval show IO Unit from do
  let origin (s : String) : Option String := (URI.parse! s).origin?.map toString
  expect (origin "http://example.com/a?b" == some "http://example.com") "http default port"
  expect (origin "http://example.com:80/" == some "http://example.com") "explicit default port"
  expect (origin "http://example.com:8080/" == some "http://example.com:8080") "explicit port"
  expect (origin "https://example.com/" == some "https://example.com") "https default port"
  expect (origin "https://example.com:80/" == some "https://example.com:80") "https on port 80"
  expect (origin "http://[::1]:8080/" == some "http://[::1]:8080") "IPv6 host"
  expect (origin "file:///etc/passwd" == none) "an empty host has no origin"
  expect (origin "mailto:a@example.com" == none) "no authority has no origin"
  let some o := (URI.parse! "http://example.com:8080/a").origin? | throw (IO.userError "no origin")
  expect (o.port == 8080 && o.scheme.val == "http") "origin fields"
  let some (scheme, host, port, target) := (URI.parse! "https://example.com/a/b?q=1#f").toOriginRequest?
    | throw (IO.userError "no origin request")
  expect (scheme.val == "https" && toString host == "example.com" && port == 443 &&
    toString target == "/a/b?q=1") "toOriginRequest? fields"
  expect ((URI.parse! "file:///x").toOriginRequest?).isNone "toOriginRequest? with an empty host"

-- A `Body.Any` coerces to itself, so an API taking any body that coerces to `Body.Any` takes it.
def takesAny [Coe β Body.Any] (b : β) : Body.Any := b

#eval show IO Unit from Async.block do
  let body : Body.Any := Body.Any.ofBody (← Body.mkStream)
  expect ((← Body.isClosed (takesAny body)) == false) "coerced body differs"

import Std.Http

/-!
Tests the HTTP client's proxy and authentication policies: `ProxySelector` (`direct`, `of`,
`bypassing`), `Challenge` (the header a challenge comes in and the one its answer goes in), and
`Authenticator` (`const`, `proxy`, `orElse`, `restrict`), including that a server credential never
reaches a proxy or another origin, and a proxy credential never reaches a server; and `Interceptor`,
whose default hooks change nothing and whose `onRequest` can rewrite a request or fail it.
-/

open Std.Http Std.Http.Client Std.Async

def origin (url : String) : URI.Origin :=
  (URI.parse! url).origin?.getD { scheme := URI.Scheme.ofString! "http", host := .empty, port := 0 }

def example80 : URI.Origin := origin "http://example.com"
def internal80 : URI.Origin := origin "http://internal.corp"
def secure443 : URI.Origin := origin "https://example.com"
def other443 : URI.Origin := origin "https://other.example"

def target : RequestTarget := RequestTarget.parse! "/"

/-! ## `ProxySelector` -/

-- `direct` never proxies.
#guard ProxySelector.direct.select example80 == Proxy.direct
#guard ProxySelector.direct.select secure443 == Proxy.direct

-- `of` proxies every origin through one endpoint.
#guard (ProxySelector.of "proxy.example" 8080).select example80 == Proxy.http "proxy.example" 8080
#guard (ProxySelector.of "proxy.example" 8080).select secure443 == Proxy.http "proxy.example" 8080

-- `bypassing` connects the origins it selects directly and defers to the selector for the rest.
def corpProxy : ProxySelector :=
  (ProxySelector.of "proxy.example" 8080).bypassing fun o => toString o.host == "internal.corp"

#guard corpProxy.select internal80 == Proxy.direct
#guard corpProxy.select example80 == Proxy.http "proxy.example" 8080

#guard (default : ProxySelector).select example80 == Proxy.direct

/-! ## `Challenge` -/

def serverChallenge : Challenge :=
  { kind := .server, origin := example80, method := .get, target, headers := Headers.empty }

def proxyChallenge : Challenge :=
  { kind := .proxy, origin := example80, method := .get, target, headers := Headers.empty,
    proxy := .http "proxy.example" 8080 }

-- A challenge names the header it was read from and the header its answer is sent in.
#guard serverChallenge.challengeHeader == Header.Name.wwwAuthenticate
#guard serverChallenge.credentialHeader == Header.Name.authorization
#guard proxyChallenge.challengeHeader == Header.Name.proxyAuthenticate
#guard proxyChallenge.credentialHeader == Header.Name.proxyAuthorization

-- `offered` reads every challenge of the matching kind, in order, ignoring the other kind's header.
def bothChallenges : Headers :=
  ((Headers.empty.insert .wwwAuthenticate (.mk "Basic realm=\"a\"")).insert
    .wwwAuthenticate (.mk "Bearer")).insert .proxyAuthenticate (.mk "Basic realm=\"p\"")

#guard ({ serverChallenge with headers := bothChallenges } : Challenge).offered.map (·.value)
  == #["Basic realm=\"a\"", "Bearer"]
#guard ({ proxyChallenge with headers := bothChallenges } : Challenge).offered.map (·.value)
  == #["Basic realm=\"p\""]
#guard serverChallenge.offered.isEmpty

-- Without a redirect, the origin the caller addressed is the challenged one.
#guard serverChallenge.initialOrigin == example80

/-! ## `Authenticator` -/

def token : Header.Value := .mk "Bearer abc123"
def proxyToken : Header.Value := .mk "Basic cHJveHk6cHc="

def answer (authenticator : Authenticator) (challenge : Challenge) : IO (Option String) := do
  return (← (authenticator.authenticate challenge).block).map (·.value)

-- `const` answers server challenges only, and `proxy` proxy challenges only, so neither kind of
-- credential reaches the other kind of peer.
#eval show IO Unit from do
  unless (← answer (.const token) serverChallenge) == some "Bearer abc123" do
    throw <| IO.userError "const must answer a server challenge"
  unless (← answer (.const token) proxyChallenge) == none do
    throw <| IO.userError "const must not answer a proxy challenge"
  unless (← answer (.proxy proxyToken) proxyChallenge) == some "Basic cHJveHk6cHc=" do
    throw <| IO.userError "proxy must answer a proxy challenge"
  unless (← answer (.proxy proxyToken) serverChallenge) == none do
    throw <| IO.userError "proxy must not answer a server challenge"

-- `const` declines a challenge from an origin a redirect led to, so the credential does not
-- follow the request to another host.
#eval show IO Unit from do
  let redirected := { serverChallenge with origin := other443, initialOrigin := example80 }
  unless (← answer (.const token) redirected) == none do
    throw <| IO.userError "const must not answer a challenge from another origin"

-- `proxy` with `only` answers that proxy alone.
#eval show IO Unit from do
  let onlyThis := Authenticator.proxy proxyToken (only := some (.http "proxy.example" 8080))
  unless (← answer onlyThis proxyChallenge) == some "Basic cHJveHk6cHc=" do
    throw <| IO.userError "proxy with `only` must answer its proxy"
  let otherProxy := { proxyChallenge with proxy := .http "evil.example" 8080 }
  unless (← answer onlyThis otherProxy) == none do
    throw <| IO.userError "proxy with `only` must not answer another proxy"

-- `orElse` asks the second only when the first declines.
#eval show IO Unit from do
  let both := (Authenticator.const token).orElse (.proxy proxyToken)
  unless (← answer both serverChallenge) == some "Bearer abc123" do
    throw <| IO.userError "orElse must use the first answer"
  unless (← answer both proxyChallenge) == some "Basic cHJveHk6cHc=" do
    throw <| IO.userError "orElse must fall back to the second"

-- `restrict` declines challenges rejected by the predicate.
#eval show IO Unit from do
  let both := (Authenticator.const token).orElse (.proxy proxyToken)
  let serverOnly := both.restrict (·.kind == Challenge.Kind.server)
  unless (← answer serverOnly serverChallenge).isSome do
    throw <| IO.userError "restrict must keep challenges accepted by the predicate"
  unless (← answer serverOnly proxyChallenge).isNone do
    throw <| IO.userError "restrict must decline challenges rejected by the predicate"

/-! ## `Interceptor` -/

def getRoot : Request.Head := { method := .get, version := .v11, uri := target }

-- The default hooks change nothing.
#eval show IO Unit from do
  let interceptor : Interceptor := {}
  let result ← (interceptor.onRequest example80 getRoot).block
  let unchanged : Bool := match result with
    | .ok head => toString head.uri == "/" && head.method == .get
    | .error _ => false
  unless unchanged do
    throw <| IO.userError "the default onRequest must return the request as it is"
  (interceptor.onResponse example80 getRoot { status := .ok }).block
  (interceptor.onInformational example80 getRoot { status := .earlyHints }).block

-- `onRequest` can rewrite a request, for the origin it is sent to only.
#eval show IO Unit from do
  let interceptor : Interceptor := {
    onRequest := fun origin head => pure <| .ok <|
      if origin == example80 then { head with headers := head.headers.insert .authorization token }
      else head }
  let ownHost ← (interceptor.onRequest example80 getRoot).block
  let otherHost ← (interceptor.onRequest other443 getRoot).block
  let rewritten : Bool := match ownHost with | .ok head => head.headers.contains .authorization | _ => false
  unless rewritten do
    throw <| IO.userError "onRequest must rewrite the request"
  let untouched : Bool := match otherHost with | .ok head => !head.headers.contains .authorization | _ => false
  unless untouched do
    throw <| IO.userError "onRequest sees the origin and leaves other hosts alone"

-- Or fail it with a client error.
#eval show IO Unit from do
  let interceptor : Interceptor := { onRequest := fun _ _ => pure (.error (.invalidRequest "blocked")) }
  let failed : Bool := match ← (interceptor.onRequest example80 getRoot).block with
    | .error (.invalidRequest "blocked") => true
    | _ => false
  unless failed do
    throw <| IO.userError "onRequest must be able to fail the request"

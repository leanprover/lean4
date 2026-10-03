import Std.Http

/-!
Exercises the client-side policy hooks in `Std.Http.Client.Config`: `ProxySelector`,
`Authenticator`, and `CookieHandler`. Each `#guard`/`#eval` asserts an observable outcome of a
selector or handler; a failing assertion throws.
-/

open Std.Http Std.Http.Client Std.Async

private def hostName (host : String) : URI.Host :=
  match URI.DomainName.ofString? host with
  | some name => .name name
  | none => panic! s!"invalid domain name: {host}"

private def mkOrigin (scheme : String) (host : String) (port : UInt16) : URI.Origin :=
  { scheme := URI.Scheme.ofString! scheme, host := hostName host, port }

private def example80 : URI.Origin := mkOrigin "http" "example.com" 80
private def internal80 : URI.Origin := mkOrigin "http" "internal.corp" 80
private def secure443 : URI.Origin := mkOrigin "https" "example.com" 443

private def target : RequestTarget := .originForm { segments := #[], absolute := true } none

/-! ## `ProxySelector` -/

-- `direct` never proxies.
#guard ProxySelector.direct.select example80 == Proxy.direct
#guard ProxySelector.direct.select secure443 == Proxy.direct

-- `of` proxies every origin through one endpoint.
#guard (ProxySelector.of "proxy.example" 8080).select example80 == Proxy.http "proxy.example" 8080
#guard (ProxySelector.of "proxy.example" 8080).select secure443 == Proxy.http "proxy.example" 8080

-- `bypassing` overrides the underlying selector with a direct connection.
private def corpProxy : ProxySelector :=
  (ProxySelector.of "proxy.example" 8080).bypassing fun o => toString o.host == "internal.corp"

#guard corpProxy.select internal80 == Proxy.direct
#guard corpProxy.select example80 == Proxy.http "proxy.example" 8080

-- The default `Config` makes no proxy connections.
#guard ({} : Client.Config).proxySelector.select example80 == Proxy.direct

/-! ## `Challenge` -/

private def serverChallenge : Challenge :=
  { kind := .server, origin := example80, target, headers := Headers.empty }

private def proxyChallenge : Challenge :=
  { kind := .proxy, origin := example80, target, headers := Headers.empty }

-- A challenge names the header it was read from and the header its answer is sent in.
#guard serverChallenge.challengeHeader == Header.Name.wwwAuthenticate
#guard serverChallenge.credentialHeader == Header.Name.authorization
#guard proxyChallenge.challengeHeader == Header.Name.proxyAuthenticate
#guard proxyChallenge.credentialHeader == Header.Name.proxyAuthorization

-- `offered` reads every challenge of the matching kind, ignoring the other kind's header.
private def bothChallenges : Headers :=
  ((Headers.empty.insert .wwwAuthenticate (.mk "Basic realm=\"a\"")).insert
    .wwwAuthenticate (.mk "Bearer")).insert .proxyAuthenticate (.mk "Basic realm=\"p\"")

#guard ({ serverChallenge with headers := bothChallenges } : Challenge).offered.map (·.value)
  == #["Basic realm=\"a\"", "Bearer"]
#guard ({ proxyChallenge with headers := bothChallenges } : Challenge).offered.map (·.value)
  == #["Basic realm=\"p\""]
#guard serverChallenge.offered.isEmpty

/-! ## `Authenticator` -/

private def token : Header.Value := .mk "Bearer abc123"

-- `const` answers every challenge with the same credential.
#eval show IO Unit from do
  let value ← (Authenticator.const token).authenticate serverChallenge |>.block
  unless value.map (·.value) == some "Bearer abc123" do
    throw <| IO.userError "const authenticator must answer a server challenge"
  let value ← (Authenticator.const token).authenticate proxyChallenge |>.block
  unless value.map (·.value) == some "Bearer abc123" do
    throw <| IO.userError "const authenticator must answer a proxy challenge"

-- `restrict` declines challenges rejected by the predicate.
#eval show IO Unit from do
  let serverOnly := (Authenticator.const token).restrict (·.kind == Challenge.Kind.server)
  let value ← serverOnly.authenticate serverChallenge |>.block
  unless value.isSome do
    throw <| IO.userError "restrict must keep challenges accepted by the predicate"
  let value ← serverOnly.authenticate proxyChallenge |>.block
  unless value.isNone do
    throw <| IO.userError "restrict must decline challenges rejected by the predicate"

-- No authenticator is configured by default.
#guard ({} : Client.Config).authenticator.isNone

/-! ## `CookieHandler` -/

-- A handler observes `store` and replays what it recorded from `load`.
#eval show IO Unit from do
  let jar ← IO.mkRef (#[] : Array Header.Value)
  let handler : CookieHandler :=
    { load := fun _ _ => return (← jar.get),
      store := fun _ _ headers => jar.modify (· ++ (headers.getAll? .setCookie).getD #[]) }
  let response := (Headers.empty.insert .setCookie (.mk "a=1")).insert .setCookie (.mk "b=2")
  handler.store example80 target response |>.block
  let sent ← handler.load example80 target |>.block
  unless sent.map (·.value) == #["a=1", "b=2"] do
    throw <| IO.userError s!"cookie handler replayed {sent.map (·.value)}"

-- No cookie handler is configured by default.
#guard ({} : Client.Config).cookieHandler.isNone

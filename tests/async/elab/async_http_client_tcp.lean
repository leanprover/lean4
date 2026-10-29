module

import Std.Http.Test.Helpers

/-! End-to-end HTTP client tests over loopback TCP against `Std.Http.Server`: the default
`Connector.tcp` with IPv4 and IPv6 literal hosts and a host name, connection reuse, and connect
failures. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-- Answers with the request target and the client's port, so a test can tell which connection
carried a request. -/
def echoPeer (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  let port := match req.extensions.get Server.RemoteAddr with
    | some { addr := .v4 a } => toString a.port
    | some { addr := .v6 a } => toString a.port
    | none => "?"
  Response.ok |>.text s!"{req.line.uri} {port}"

def boundPort (server : Server) : Async UInt16 := do
  match server.localAddr with
  | some (.v4 a) => pure a.port
  | some (.v6 a) => pure a.port
  | none => throw (IO.userError "the server reported no local address")

def tcpOrigin (host : URI.Host) (port : UInt16) : URI.Origin :=
  { scheme := URI.Scheme.ofString! "http", host, port }

def getBody (client : Client) (target : URI.Origin) (path : String) : Async String := do
  let request ← Request.new |>.method .get |>.uri! path |>.empty
  let response ← client.send target request
  response.body.readAll (α := String)

def loopback4 : Net.IPv4Addr := Net.IPv4Addr.ofParts 127 0 0 1
def loopback6 : Net.IPv6Addr := Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 1

-- An IPv4 literal host, and the client reusing its connection for a second request.
#eval show IO _ from runWithTimeout "GET over IPv4 loopback reuses the connection" 5000 <|
  Async.block do
  let server ← Server.serve (.v4 ⟨loopback4, 0⟩) echoPeer
  let target := tcpOrigin (.ipv4 loopback4) (← boundPort server)
  let client ← Client.new
  let first ← getBody client target "/a"
  let second ← getBody client target "/b"
  server.shutdownAndWait
  let firstPort := (first.splitOn " ")[1]!
  unless first.startsWith "/a " && second.startsWith "/b " do
    throw (IO.userError s!"unexpected bodies {first.quote} {second.quote}")
  unless second.endsWith s!" {firstPort}" do
    throw (IO.userError s!"the second request used a new connection: {first.quote} then {second.quote}")

-- An IPv6 literal host is dialled directly; the resolver would reject its bracketed form. Skipped
-- where the machine has no IPv6 loopback.
#eval show IO _ from runWithTimeout "GET over an IPv6 literal host" 5000 <|
  Async.block do
  let server ← try some <$> Server.serve (.v6 ⟨loopback6, 0⟩) echoPeer catch _ => pure none
  let some server := server | return
  let target := tcpOrigin (.ipv6 loopback6) (← boundPort server)
  let client ← Client.new
  let body ← getBody client target "/v6"
  server.shutdownAndWait
  unless body.startsWith "/v6 " do
    throw (IO.userError s!"unexpected body {body.quote}")

-- A host name goes through the resolver.
#eval show IO _ from runWithTimeout "GET to localhost by name" 5000 <|
  Async.block do
  let server ← Server.serve (.v4 ⟨loopback4, 0⟩) echoPeer
  let some name := URI.DomainName.ofString? "localhost"
    | throw (IO.userError "localhost did not parse as a domain name")
  let target := tcpOrigin (.name name) (← boundPort server)
  let client ← Client.new
  let body ← getBody client target "/named"
  server.shutdownAndWait
  unless body.startsWith "/named " do
    throw (IO.userError s!"unexpected body {body.quote}")

-- Nothing listening gives a typed connect error.
#eval show IO _ from runWithTimeout "a refused connection is a connect error" 5000 <|
  Async.block do
  let server ← Server.serve (.v4 ⟨loopback4, 0⟩) echoPeer
  let port ← boundPort server
  server.shutdownAndWait
  let client ← Client.new (maxRetries := 0)
  let request ← Request.new |>.method .get |>.uri! "/" |>.empty
  match ← client.trySend (tcpOrigin (.ipv4 loopback4) port) request with
  | .error (.connect _) => pure ()
  | .error e => throw (IO.userError s!"expected a connect error, got {e}")
  | .ok _ => throw (IO.userError "a request to a closed port succeeded")

-- The default connector speaks plain HTTP only.
#eval show IO _ from runWithTimeout "https is refused by the default connector" 5000 <|
  Async.block do
  let client ← Client.new (maxRetries := 0)
  let request ← Request.new |>.method .get |>.uri! "/" |>.empty
  let target : URI.Origin := { scheme := URI.Scheme.ofString! "https", host := .ipv4 loopback4, port := 443 }
  match ← client.trySend target request with
  | .error (.connect message) =>
    unless message.contains "https" do throw (IO.userError s!"unexpected message {message}")
  | .error e => throw (IO.userError s!"expected a connect error, got {e}")
  | .ok _ => throw (IO.userError "an https request succeeded over plain TCP")

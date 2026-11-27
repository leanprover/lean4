import Std.Http

/-!
Tests the HTTP client hop driver (`Std.Http.Client.Hop.Driver`) without I/O: responses delivered to the
caller, redirects followed (method rewrites, bodies, `Expect`, other origins), the redirect budget
and cycles, retries on fresh connections and when a request may be sent again, and failures; then
the redirect rules of RFC 9110 §15.4 status by status, how `Location` is resolved, the header fields
a redirect drops, and the methods RFC 9110 §9.2.2 lets a retry repeat.
-/

open Std.Http Std.Http.Client Std.Http.Client.Hop.Driver

def origin (host : String) : URI.Origin :=
  (URI.parse! s!"http://{host}/").origin?.getD
    { scheme := URI.Scheme.ofString! "http", host := .empty, port := 0 }

def a := origin "a"
def b := origin "b"

def request (method : Method) (path : String := "/a") (headers : Headers := .empty) : Request.Head :=
  { method, version := .v11, uri := RequestTarget.parse! path, headers }

def response (status : Status) (location : Option String := none) : Response.Head :=
  { status, headers := match location with
      | some l => Headers.empty.insert .location (.ofString! l)
      | none => .empty }

def tags (cmds : Array Command) : List String :=
  cmds.toList.map fun
    | .send o head body fresh =>
      s!"send {o.host} {head.method} {head.uri} {repr body}{if fresh then " fresh" else ""}"
    | .drain => "drain"
    | .release reusable => s!"release {reusable}"
    | .deliver => "deliver"
    | .fail err => s!"fail {err}"

def run (s : State) (inputs : List Input) : State × List String :=
  inputs.foldl (init := (s, [])) fun (s, out) input =>
    let (s, cmds) := step s input
    (s, out ++ tags cmds)

def get (path : String := "/a") (maxRedirects := 10) (maxRetries := 1) : State :=
  init a (request .get path) true maxRedirects maxRetries

def redirected (status : Status) (location : String) : List Input :=
  [.responded (response status (some location)), .drained (.ok true)]

/-! ## Delivered responses -/

#guard (run (get) [.start, .responded (response .ok)]).2 ==
  ["send a GET /a Std.Http.Client.Hop.Driver.BodySource.original", "deliver"]

-- A 3xx that is not a followed redirect, or one with no `Location`, is the caller's.
#guard (run (get) [.start, .responded (response .notModified (some "/b"))]).2.getLast? == some "deliver"
#guard (run (get) [.start, .responded (response .found)]).2.getLast? == some "deliver"

/-! ## Following redirects -/

-- The redirect's body is drained, its connection given back, and the next hop sent.
#guard (run (get) ([.start] ++ redirected .found "/b")).2 ==
  ["send a GET /a Std.Http.Client.Hop.Driver.BodySource.original", "drain", "release true",
   "send a GET /b Std.Http.Client.Hop.Driver.BodySource.empty"]

-- A connection that cannot carry another request is given back as such.
#guard (run (get) [.start, .responded (response .found (some "/b")), .drained (.ok false)]).2.contains
  "release false"

-- 303 turns a POST into a GET without content, and drops `Expect: 100-continue`.
#guard
  let s := init a (request .post "/a" (Headers.empty.insert .expect (.mk "100-continue"))) true 10 1
  let (s, out) := run s ([.start] ++ redirected .seeOther "/b")
  out.getLast? == some "send a GET /b Std.Http.Client.Hop.Driver.BodySource.empty" &&
    !s.head.headers.contains .expect

-- 307 resends a POST with its body rewound...
#guard (run (init a (request .post) true 10 1) ([.start] ++ redirected .temporaryRedirect "/b")).2.getLast? ==
  some "send a POST /b Std.Http.Client.Hop.Driver.BodySource.rewound"

-- ...but not a body that cannot be rewound: the 307 is the caller's.
#guard (run (init a (request .post) false 10 1)
    [.start, .responded (response .temporaryRedirect (some "/b"))]).2.getLast? == some "deliver"

-- A redirect to another origin is sent there.
#guard (run (get) ([.start] ++ redirected .found "http://b/x")).2.getLast? ==
  some "send b GET http://b/x Std.Http.Client.Hop.Driver.BodySource.empty"

/-! ## The redirect budget and cycles -/

#guard (run (get (maxRedirects := 1)) ([.start] ++ redirected .found "/b" ++
    [.responded (response .found (some "/c"))])).2.getLast? == some "deliver"

-- A chain that comes back to a target it already sent the same method to stops there.
#guard (run (get) ([.start] ++ redirected .found "/b" ++
    [.responded (response .found (some "/a"))])).2.getLast? == some "deliver"

-- A POST answered with 303 to its own URL is followed with GET: the method is part of what was visited.
#guard (run (init a (request .post) true 10 1) ([.start] ++ redirected .seeOther "/a")).2.getLast? ==
  some "send a GET /a Std.Http.Client.Hop.Driver.BodySource.empty"

/-! ## Retries -/

-- A retryable failure of an idempotent request with a body that rewinds is retried on a fresh
-- connection, from the first hop, with its body rewound.
#guard (run (get) [.start, .failed (.closed "reset") false]).2.getLast? ==
  some "send a GET /a Std.Http.Client.Hop.Driver.BodySource.rewound fresh"

-- After a redirect, the retry starts over at the origin the caller addressed.
#guard (run (get) ([.start] ++ redirected .found "http://b/x" ++ [.failed (.closed "reset") false])).2.getLast? ==
  some "send a GET /a Std.Http.Client.Hop.Driver.BodySource.rewound fresh"

-- Retries run out.
#guard (run (get (maxRetries := 1)) [.start, .failed (.closed "x") false, .failed (.closed "y") false]).2.getLast? ==
  some "fail y"

-- A failure a fresh connection would repeat is not retried.
#guard (run (get) [.start, .failed .timeout false]).2.getLast? == some "fail request timeout"

-- Nor is any request once the client was closed.
#guard (run (get) [.start, .failed (.closed "x") true]).2.getLast? == some "fail x"

-- A POST that may have reached the peer is not sent again...
#guard (run (init a (request .post) true 10 1) [.start, .failed (.closed "x") false]).2.getLast? ==
  some "fail x"

-- ...but one that provably never left is, its body as it stands when it cannot be rewound.
#guard (run (init a (request .post) false 10 1) [.start, .failed (.notSent "x") false]).2.getLast? ==
  some "send a POST /a Std.Http.Client.Hop.Driver.BodySource.original fresh"

-- Not once a hop of the attempt got a response: the request it was redirected from reached a peer.
#guard (run (init a (request .post) true 10 1) ([.start] ++ redirected .seeOther "/b" ++
    [.failed (.notSent "x") false])).2.getLast? == some "fail x"

/-! ## Failures -/

-- A redirect body that fails gives its connection up, and fails the request.
#guard (run (get) [.start, .responded (response .found (some "/b")), .drained (.error (.closed "cut"))]).2 ==
  ["send a GET /a Std.Http.Client.Hop.Driver.BodySource.original", "drain", "release false", "fail cut"]

-- An absolute-form target for another origin is never sent.
#guard (run (init a (request .get "http://b/x") true 10 1) [.start]).2 ==
  ["fail request target http://b/x does not belong to the origin it is sent to, http://a"]

-- A request that is over ignores every input.
#guard
  let (s, _) := run (get) [.start, .responded (response .ok)]
  (step s (.responded (response .ok))).2.isEmpty && (step s .start).2.isEmpty

/-! ## RFC 9110 §15.4, status by status -/

/-- The last command after `inputs`. -/
def lastAfter (s : State) (inputs : List Input) : Option String := (run s inputs).2.getLast?

def send (method : String) (target : String) (body : String) : Option String :=
  some s!"send a {method} {target} Std.Http.Client.Hop.Driver.BodySource.{body}"

-- 301 and 302 may turn a POST into a GET (RFC 9110 §15.4.2, §15.4.3), which drops its content...
#guard lastAfter (init a (request .post) true 10 1) ([.start] ++ redirected .movedPermanently "/b") ==
  send "GET" "/b" "empty"
#guard lastAfter (init a (request .post) true 10 1) ([.start] ++ redirected .found "/b") ==
  send "GET" "/b" "empty"

-- ...but keep every other method, and its content.
#guard lastAfter (init a (request .put) true 10 1) ([.start] ++ redirected .found "/b") ==
  send "PUT" "/b" "rewound"

-- 308 keeps the method and the content (RFC 9110 §15.4.9).
#guard lastAfter (init a (request .post) true 10 1) ([.start] ++ redirected .permanentRedirect "/b") ==
  send "POST" "/b" "rewound"

-- 303 turns every method but HEAD into GET (RFC 9110 §15.4.4).
#guard lastAfter (init a (request .head) true 10 1) ([.start] ++ redirected .seeOther "/b") ==
  send "HEAD" "/b" "empty"
#guard lastAfter (init a (request .delete) true 10 1) ([.start] ++ redirected .seeOther "/b") ==
  send "GET" "/b" "empty"

-- 300 and the deprecated 305 are the caller's, `Location` or not (RFC 9110 §15.4.1, §15.4.6).
#guard lastAfter (get) [.start, .responded (response .multipleChoices (some "/b"))] == some "deliver"
#guard lastAfter (get) [.start, .responded (response .useProxy (some "/b"))] == some "deliver"

-- With no redirects allowed, every redirect is the caller's.
#guard lastAfter (get (maxRedirects := 0)) [.start, .responded (response .found (some "/b"))] ==
  some "deliver"

/-! ## Resolving `Location` (RFC 9110 §10.2.2, RFC 3986 §5) -/

#guard lastAfter (get "/x/y") ([.start] ++ redirected .found "../b") == send "GET" "/b" "empty"
#guard lastAfter (get "/x/y") ([.start] ++ redirected .found "?q=1") == send "GET" "/x/y?q=1" "empty"

-- A network-path reference names another origin.
#guard lastAfter (get) ([.start] ++ redirected .found "//b/x") ==
  some "send b GET http://b/x Std.Http.Client.Hop.Driver.BodySource.empty"

-- A fragment is never sent (RFC 9110 §4.2.4).
#guard lastAfter (get) ([.start] ++ redirected .found "/b#frag") == send "GET" "/b" "empty"

-- A `Location` that is not a URI reference leaves the response to the caller.
#guard lastAfter (get) [.start, .responded (response .found (some "http://[bad"))] == some "deliver"

/-! ## The header fields a redirect drops -/

def fieldsAfter (s : State) (inputs : List Input) : List String :=
  (run s inputs).1.head.headers.toList.map fun (name, _) => name.value

def credentials : Headers :=
  (Headers.empty.insert .authorization (.mk "Basic x")).insert (Header.Name.ofString! "cookie") (.mk "s=1")

-- Credentials stay within the origin they were given for...
#guard fieldsAfter (init a (request .get "/a" credentials) true 10 1) ([.start] ++ redirected .found "/b") ==
  ["authorization", "cookie"]

-- ...and are dropped on a hop to another one, a change of scheme included.
#guard fieldsAfter (init a (request .get "/a" credentials) true 10 1)
    ([.start] ++ redirected .found "http://b/x") == []
#guard fieldsAfter (init a (request .get "/a" credentials) true 10 1)
    ([.start] ++ redirected .found "https://a/x") == []

def content : Headers :=
  (Headers.empty.insert .contentType (.mk "text/plain")).insert .contentLength (.mk "3")

-- A redirect to GET drops the fields that described the content (RFC 9110 §15.4); one that keeps
-- the content keeps them.
#guard fieldsAfter (init a (request .post "/a" content) true 10 1) ([.start] ++ redirected .seeOther "/b") == []
#guard fieldsAfter (init a (request .post "/a" content) true 10 1)
    ([.start] ++ redirected .temporaryRedirect "/b") == ["content-type", "content-length"]

/-! ## Retries (RFC 9110 §9.2.2) -/

-- An idempotent method is retried...
#guard lastAfter (init a (request .put) true 10 1) [.start, .failed (.closed "x") false] ==
  some "send a PUT /a Std.Http.Client.Hop.Driver.BodySource.rewound fresh"

-- ...one that is not, never once it may have been sent.
#guard lastAfter (init a (request .patch) true 10 1) [.start, .failed (.closed "x") false] ==
  some "fail x"

-- With no retries allowed, the first failure is the request's.
#guard lastAfter (get (maxRetries := 0)) [.start, .failed (.closed "x") false] == some "fail x"

-- Every hop of a retry asks for a fresh connection, its redirects included.
#guard (run (get) ([.start, .failed (.closed "x") false] ++ redirected .found "/b")).2.getLast? ==
  some "send a GET /b Std.Http.Client.Hop.Driver.BodySource.empty fresh"

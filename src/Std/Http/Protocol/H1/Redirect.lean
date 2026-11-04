/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data.Request
public import Std.Http.Data.Status
public import Std.Http.Data.URI

public section

/-!
# Redirect planning

Pure HTTP redirect-decision logic.

`decideRedirect` inspects a response-line `Status` and `Location` header and produces a
`RedirectOutcome` describing whether to stop or follow, plus the full rewrite required by RFC 9110
§15.4 (Redirect 3xx) and RFC 9112 §3.2 (Request Target).

This module never touches `IO` or `Async`.

References:
* https://httpwg.org/specs/rfc9110.html#status.3xx
* https://httpwg.org/specs/rfc9112.html#section-3.2
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
What the caller must do with the body of the original request when following a redirect.
-/
inductive RedirectBodyAction where

  /--
  Send an empty body on the redirected request. Chosen when the redirected request is a `GET` or
  `HEAD`: the method changed (303 See Other, or 301/302 on `POST`), or it already was one.
  -/
  | empty

  /--
  Reset the original body and resend it on the redirected request. Chosen when the redirect keeps a
  method other than `GET` or `HEAD` (307/308, and 301/302 on methods other than `POST`); such a
  redirect is only followed when the body is marked replayable.
  -/
  | replay
deriving DecidableEq, Repr, Inhabited

/--
The concrete work the caller must perform to follow a redirect.
-/
structure RedirectPlan where

  /--
  Target origin (scheme, host, port) for the redirected request.
  -/
  origin : URI.Origin

  /--
  Rewritten request target put on the wire: origin-form for same-origin redirects, absolute-form
  for cross-origin redirects, with any `userinfo` stripped per RFC 9110 §4.2.4.
  -/
  target : RequestTarget

  /--
  Method to use for the redirected request (possibly downgraded to `GET` for 301/302 on `POST` or
  for 303).
  -/
  method : Method

  /--
  Headers for the redirected request after cross-origin and method-change scrubbing.
  -/
  headers : Headers

  /--
  What to do with the original request body.
  -/
  bodyAction : RedirectBodyAction

  /--
  Whether the redirect crosses origin boundaries (different host, port, or scheme). Useful for
  credential-handling decisions at the call site.
  -/
  isCrossOrigin : Bool
deriving Repr

/--
Result of evaluating whether to follow a redirect.
-/
inductive RedirectOutcome where

  /--
  Response is final. Stop redirecting and return it.
  -/
  | done

  /--
  Follow the redirect described by `plan`.
  -/
  | follow (plan : RedirectPlan)
deriving Inhabited

namespace RedirectPlan

/--
Resolves the target origin for a redirect (RFC 3986 §5.2.2), or `none` when the reference names no
host to connect to.

* **Absolute URI**: scheme and authority come directly from the URI. Per RFC 3986 §5.2.2 an
  absolute reference takes its authority from the reference and does not inherit the base's, so an
  absolute URL without an authority resolves to `none`.

* **Protocol-relative reference** (`//host/path`): authority comes from the reference,
  scheme is inherited from `current` (RFC 3986 §5.2.2, R.authority defined).

* **Path/query/fragment-only reference**: no authority in the reference, so the full
  origin is inherited from `current` — the redirect is same-origin.
-/
private def resolveOrigin (current : URI.Origin) : URIReference → Option URI.Origin
  | .absolute af =>
    af.authority.map fun auth =>
      let port : UInt16 :=
        match auth.port with
        | .value v => v
        | _ => URI.Scheme.defaultPort af.scheme
      { scheme := af.scheme, host := auth.host, port }

  | .relative { authority := some auth, .. } =>
    let port : UInt16 :=
      match auth.port with
      | .value v => v
      | _ => URI.Scheme.defaultPort current.scheme

    some { scheme := current.scheme, host := auth.host, port }

  | .relative _ =>
    some current

/--
Computes the method for the redirected request (RFC 9110 §15.4): 303 becomes GET (but HEAD is
preserved, since a 303 may be retrieved with GET or HEAD per RFC 9110 §15.4.4); 301/302 downgrade
POST to GET (prevailing practice, explicitly permitted by RFC 9110); 307/308 preserve the original
method.
-/
private def chooseMethod (originalMethod : Method) : Status → Method
  | .seeOther =>

    -- https://httpwg.org/specs/rfc9110.html#status.303
    -- 303 may be retrieved with GET or HEAD, so a HEAD request keeps HEAD; everything else uses GET.
    if originalMethod == .head then .head else .get
  | .movedPermanently | .found =>

    -- https://httpwg.org/specs/rfc9110.html#status.301
    -- https://httpwg.org/specs/rfc9110.html#status.302

    -- The downgrade does not depend on the response's version: a version says what the server
    -- speaks, not what its redirect means, and keeping POST would replay the body to the target.
    if originalMethod == .post then .get
    else originalMethod

  | _ => originalMethod

/--
Connection-specific fields that must not be forwarded across hops regardless of origin.
-/
private def connectionHeaders : Array Header.Name :=
  #[.connection, .keepAlive, .transferEncoding]

/--
Additional hop-by-hop fields nominated by the request's `Connection` header.

Invalid `Connection` values are ignored here: the fixed hop-by-hop header names are still stripped,
and the redirect planner does not reject an otherwise-followable response based on request-header
syntax that may already have been accepted by a caller.
-/
private def nominatedConnectionHeaders (headers : Headers) : Array Header.Name :=
  match headers.getAll? .connection with
  | none => #[]
  | some values =>
    values.foldl (init := #[]) fun names value =>
      match Header.Connection.parse value with
      | none => names
      | some connection =>
        connection.tokens.foldl (init := names) fun names token =>
          match Header.Name.ofString? token with
          | none => names
          | some name => names.push name

/--
Proxy-configuration headers that must not cross origins.
-/
private def clientProxyHeaders : Array Header.Name :=
  #[.proxyAuthorization]

/--
Origin-specific credential headers stripped on cross-origin hops.
Note: `.origin` is intentionally excluded — it is set by the caller (e.g. for CORS), not
auto-generated by the implementation. Stripping a user-set Origin would break intentional
cross-origin requests.
-/
private def originHeaders : Array Header.Name :=
  #[.authorization, .cookie, .referer]

/--
Cache-validating headers added by the implementation that must not be replayed on the redirected
request.
-/
private def validatingHeaders : Array Header.Name :=
  #[.ifNoneMatch, .ifModifiedSince]

/--
Resource-specific headers that become meaningless when the method changes to GET/HEAD and no body
is sent.
-/
private def resourceSpecificHeaders : Array Header.Name :=
  #[.contentType, .contentLength, .contentEncoding, .contentLanguage, .contentLocation, .lastModified]

/--
Strips headers that must not survive a cross-origin hop or a method-changing
redirect per RFC 9110 §15.4.

Cross-origin: removes connection-specific, proxy-configuration, origin-specific,
and cache-validating header groups.

Method change (to GET/HEAD): removes resource-specific content headers because
the redirected request carries no body.
-/
-- `methodChanged` is only ever set when the method changed to GET: `chooseMethod` never
-- produces any other new method, so a changed method is always a change "to safe".
private def scrubHeaders (headers : Headers) (isCrossOrigin methodChanged : Bool) : Headers :=
  let afterConnection := connectionHeaders ++ nominatedConnectionHeaders headers

  let afterOrigin :=

    -- https://httpwg.org/specs/rfc9110.html#status.3xx
    -- Remove header fields that were automatically generated by the implementation,
    -- replacing them with updated values as appropriate to the new request.
    if isCrossOrigin then
      afterConnection ++ clientProxyHeaders ++ originHeaders ++ validatingHeaders
    else
      afterConnection

  -- https://httpwg.org/specs/rfc9110.html#status.3xx
  -- If the request method has been changed to GET or HEAD, remove content-specific header
  -- fields, including (but not limited to) Content-Encoding, Content-Language, Content-Location,
  -- Content-Type, Content-Length, Digest, Last-Modified.
  -- Also strip cache-validating headers (If-None-Match, If-Modified-Since) when the method
  -- changes to GET/HEAD: the original conditional request targets a specific resource state
  -- that may not apply to the redirect destination.
  let afterMethod :=
    if methodChanged then
      afterOrigin ++ resourceSpecificHeaders ++ validatingHeaders
    else
      afterOrigin

  headers.eraseMany afterMethod

/--
Rewrites the `Host` header for a cross-origin redirect. The redirected request is dispatched on a
fresh connection to `(scheme, host, port)`; the original `Host` would route the request to the wrong
virtual host.
-/
private def rewriteHostHeader (headers : Headers) (origin : URI.Origin) : Headers :=
  if headers.contains .host then headers.replaceLast .host (.ofString! origin.hostHeader)
  else headers

/--
Extracts the base query, preserving absence as `none`.
-/
private def requestTargetQuery? : RequestTarget → Option URI.Query
  | .originForm _ q => q
  | .absoluteForm uri => uri.query
  | _ => none

/--
The wire form of a resolved reference path.

RFC 3986 §5.2.2 applies `remove_dot_segments` in every branch of reference resolution — when the
reference carries a scheme, when it carries an authority, and when it is a bare path — so the
normalization belongs here rather than in one branch of `rewriteTarget`. RFC 9112 §3.2.1 then
requires a client to send `/` when the resolved path is empty, which is what an absolute path with
no segments renders as.
-/
private def resolvedPath (path : URI.Path) : URI.Path :=
  { path.normalize with absolute := true }

/--
Rewrites the target actually placed on the wire.
-/
private def rewriteTarget (ref : URIReference) (isCrossOrigin : Bool)
    (basePath : URI.Path) (baseQuery : Option URI.Query)
    (currentScheme : URI.Scheme) : RequestTarget :=
  match ref with
  | .absolute af =>
    -- The fragment is never placed on the wire (RFC 9112 §3.2 / RFC 9110 §7.1), so drop it here
    -- alongside any `userinfo` in the authority.
    let stripped :=
      { af with
        path := resolvedPath af.path,
        authority := af.authority.map (fun auth => { auth with userInfo := none }),
        fragment := none }
    if isCrossOrigin then
      .absoluteForm stripped
    else
      .originForm stripped.path stripped.query
  | .relative { authority := some auth, path, query, .. } =>

    -- Protocol-relative: authority present, scheme inherited from current.
    let path := resolvedPath path
    let stripped := { auth with userInfo := none }
    let af := { scheme := currentScheme, authority := some stripped, path, query, fragment := none }
    if isCrossOrigin then
      .absoluteForm af
    else
      .originForm path query
  | .relative { authority := none, path := refPath, query, .. } =>

    -- RFC 3986 §5.2.2: merge base path with reference path, then normalize. `/` has no segments, so
    -- `absolute` must be tested before `isEmpty`: only a relative path with no segments is empty.
    let isEmptyPath := !refPath.absolute && refPath.isEmpty
    let merged :=
      if refPath.absolute then
        refPath
      else if isEmptyPath then
        basePath
      else
        basePath.parent.join refPath
    let rewrittenQuery :=
      if isEmptyPath && query.isNone then
        baseQuery
      else
        query
    .originForm (resolvedPath merged) rewrittenQuery

end RedirectPlan

/--
Decides whether to follow a redirect given the server's response-line status and headers, the
pending request, and whether the request body is replayable.

Returns `.done` when:
* the status is not a 3xx redirection,
* no `Location` header is present,
* the `Location` value does not parse as a URI-reference (RFC 9110 §10.2.2),
* the target names no host, or resolves to a non-`http(s)` scheme (SSRF guard),
* the redirect keeps a method other than `GET`/`HEAD` but the body cannot be replayed.

Returns `.follow plan` otherwise. The caller is expected to drain the redirect response body and,
when `plan.bodyAction == .replay`, reset the original body before dispatching the rewritten request.
On a cross-origin hop the original `Host` header is rewritten to the new origin, but only when one
was present; if the original request carried no `Host`, supplying one for the new origin is the
caller's responsibility.

Notes on specific status codes that always return `.done`:
* 300 Multiple Choices — may carry a `Location` naming the server's preferred choice, but
  RFC 9110 §15.4.1 leaves the selection to the user agent, so we deliberately do not auto-select.
* 304 Not Modified — cache revalidation result, not a navigation redirect.
* 305 Use Proxy — deprecated (RFC 9110 §15.4.6); blocked for security.
* 306 — reserved/unused.
-/
def decideRedirect
    (current : URI.Origin)
    (request : Request.Head)
    (bodyReplayable : Bool)
    (status : Status)
    (responseHeaders : Headers)
    : RedirectOutcome := Id.run do
  if !status.isRedirection then
    return .done

  -- 305 Use Proxy is deprecated (RFC 9110 §15.4.6) and carries a proxy URI in
  -- Location. Following it automatically would silently route traffic through an
  -- attacker-supplied proxy, so we treat it as a terminal response.
  -- 306 is reserved and undefined (RFC 9110 §15.4.7); auto-following it could
  -- silently act on an attacker-controlled Location header.
  -- 304 Not Modified is a cache-revalidation result, not a navigation redirect.
  -- 300 Multiple Choices may name a preferred `Location`, but RFC 9110 §15.4.1 leaves
  -- the choice to the user agent, so we deliberately decline to auto-select one.
  if status == .useProxy || status == .unused || status == .notModified || status == .multipleChoices then
    return .done

  let some locationValue := responseHeaders.get? .location
    | return .done

  -- RFC 9110 §10.2.2: Location = URI-reference (absolute URI or relative reference)
  let some location := URIReference.parse? locationValue.value
    | return .done

  let newMethod := RedirectPlan.chooseMethod request.method status

  -- An absolute `Location` with no authority (RFC 3986 §5.2.2) names no host to connect to.
  let some newOrigin := RedirectPlan.resolveOrigin current location
    | return .done

  -- SSRF guard: only http(s) origins may be auto-followed. `Scheme.val` is always
  -- lowercase-normalized (see `URI.Scheme`), so this comparison is case-insensitive.
  if newOrigin.scheme.val != "http" && newOrigin.scheme.val != "https" then
    return .done

  let isCrossOrigin := newOrigin != current
  let methodChanged := newMethod != request.method

  let scrubbed := RedirectPlan.scrubHeaders request.headers isCrossOrigin methodChanged
  let newHeaders :=
    if isCrossOrigin then
      RedirectPlan.rewriteHostHeader scrubbed newOrigin
    else scrubbed

  -- A redirect that keeps the method resends the original request (RFC 9110 §15.4), body included:
  -- 307/308 always, and 301/302 for every method but POST.
  if !methodChanged && newMethod != Method.get && newMethod != Method.head && !bodyReplayable then
    return .done

  let bodyAction : RedirectBodyAction :=
    if newMethod == Method.get || newMethod == Method.head || methodChanged then
      .empty
    else
      .replay

  let rewrittenTarget := RedirectPlan.rewriteTarget location isCrossOrigin
    request.uri.pathOrRoot
    (RedirectPlan.requestTargetQuery? request.uri)
    current.scheme

  return .follow {
    origin := newOrigin
    target := rewrittenTarget
    method := newMethod
    headers := newHeaders
    bodyAction := bodyAction
    isCrossOrigin := isCrossOrigin
  }

end Std.Http.Protocol.H1

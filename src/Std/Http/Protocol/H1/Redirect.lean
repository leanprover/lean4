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
import Std.Http.Protocol.H1.Message

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

    -- Whatever the response's HTTP version: keeping POST would replay the body to the target.
    if originalMethod == .post then .get
    else originalMethod

  | _ => originalMethod

/--
Rewrites the request headers for a redirect to `origin` per RFC 9110 §15.4.

Every hop drops the connection-specific fields and those the request's `Connection` header nominates.
Invalid `Connection` values are ignored here: the redirect planner does not reject an
otherwise-followable response based on request-header syntax that may already have been accepted by
a caller.

A cross-origin hop also drops the proxy-configuration, origin-specific credential and
cache-validating fields, and rewrites a `Host` header for `origin`: the redirected request goes to a
fresh connection, and the original `Host` would route it to the wrong virtual host.

A method change (to GET/HEAD) drops the resource-specific content fields, because the redirected
request carries no body.
-/
-- `methodChanged` is only ever set when the method changed to GET: `chooseMethod` never
-- produces any other new method, so a changed method is always a change "to safe".
private def scrubHeaders (headers : Headers) (origin : URI.Origin) (isCrossOrigin methodChanged : Bool) :
    Headers := Id.run do
  let nominated := match headers.getAll? .connection with
    | none => #[]
    | some values => (connectionOptions values).1.filterMap Header.Name.ofString?
  let mut names : Array Header.Name := #[.connection, .keepAlive, .transferEncoding] ++ nominated

  -- https://httpwg.org/specs/rfc9110.html#status.3xx
  -- Remove header fields that were automatically generated by the implementation,
  -- replacing them with updated values as appropriate to the new request.
  -- `Origin` is kept: the caller sets it (e.g. for CORS), and stripping it would break intentional
  -- cross-origin requests.
  if isCrossOrigin then
    names := names ++ #[.proxyAuthorization, .authorization, .cookie, .referer, .ifNoneMatch, .ifModifiedSince]

  -- https://httpwg.org/specs/rfc9110.html#status.3xx
  -- If the request method has been changed to GET or HEAD, remove content-specific header
  -- fields, including (but not limited to) Content-Encoding, Content-Language, Content-Location,
  -- Content-Type, Content-Length, Digest, Last-Modified.
  -- Also strip cache-validating headers (If-None-Match, If-Modified-Since) when the method
  -- changes to GET/HEAD: the original conditional request targets a specific resource state
  -- that may not apply to the redirect destination.
  if methodChanged then
    names := names ++ #[.contentType, .contentLength, .contentEncoding, .contentLanguage,
      .contentLocation, .lastModified, .ifNoneMatch, .ifModifiedSince]

  let headers := headers.eraseMany names
  return if isCrossOrigin && headers.contains .host then headers.replaceLast .host (.ofString! origin.hostHeader)
    else headers

/--
Resolves the reference `ref` against `base` (RFC 3986 §5.2.2), removing dot segments from the
resolved path. An empty reference keeps the base path as is and, without a query of its own, the
base query. The fragment is always `ref`'s.
-/
private def resolve (base : URI) : URIReference → URI
  | .absolute uri => uri.normalize
  | .relative { authority := some authority, path, query, fragment } =>
    { scheme := base.scheme, authority := some authority, path := path.normalize, query, fragment }
  | .relative { authority := none, path, query, fragment } =>
    -- `/` has no segments, so `absolute` must be tested before `isEmpty`.
    if path.absolute then
      { base with path := path.normalize, query, fragment }
    else if path.isEmpty then
      { base with query := query <|> base.query, fragment }
    else
      -- RFC 3986 §5.2.3: after an authority, an empty base path merges as `/`.
      let merged := base.path.parent.join path
      let merged := { merged with absolute := merged.absolute || base.authority.isSome }
      { base with path := merged.normalize, query, fragment }

end RedirectPlan

/--
Decides whether to follow a redirect given the server's response-line status and headers, the
pending request, and whether the request body is replayable.

Returns `.done` when:
* the status is not a 3xx redirection,
* the request is a `CONNECT`, whose target is the authority to tunnel to (RFC 9110 §9.3.6), not a
  resource a `Location` can stand in for,
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

  -- Every redirected target is origin-form or absolute-form, and CONNECT needs authority-form.
  if request.method == .connect then
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

  -- The `Location` reference resolves against the request's target URI (RFC 9110 §10.2.2).
  let base : URI := {
    scheme := current.scheme
    authority := some { host := current.host, port := .value current.port }
    path := request.uri.pathOrRoot
    query := match request.uri with
      | .originForm _ query => query
      | .absoluteForm uri => uri.query
      | _ => none
    fragment := none }
  let target := RedirectPlan.resolve base location

  -- An absolute `Location` with no authority or an empty host (RFC 3986 §5.2.2) names no host to
  -- connect to.
  let some authority := target.authority
    | return .done
  if authority.host == .empty then
    return .done
  let newOrigin : URI.Origin := { scheme := target.scheme, host := authority.host, port := target.port }

  -- SSRF guard: only http(s) origins may be auto-followed. `Scheme.val` is always
  -- lowercase-normalized (see `URI.Scheme`), so this comparison is case-insensitive.
  if newOrigin.scheme.val != "http" && newOrigin.scheme.val != "https" then
    return .done

  let isCrossOrigin := newOrigin != current
  let methodChanged := newMethod != request.method

  let newHeaders := RedirectPlan.scrubHeaders request.headers newOrigin isCrossOrigin methodChanged

  -- A redirect that keeps the method resends the original request (RFC 9110 §15.4), body included:
  -- 307/308 always, and 301/302 for every method but POST.
  let bodyAction : RedirectBodyAction :=
    if newMethod == Method.get || newMethod == Method.head || methodChanged then
      .empty
    else
      .replay

  if bodyAction matches .replay && !bodyReplayable then
    return .done

  -- The path goes on the wire without dot segments, and absolute, so that an empty path is sent as
  -- `/` (RFC 9112 §3.2.1); removing the dot segments of an empty reference's base path too is path
  -- normalization (RFC 3986 §6.2.2.3). The fragment (RFC 9112 §3.2, RFC 9110 §7.1) and `userinfo`
  -- (RFC 9110 §4.2.4) are never sent.
  let path := { target.path.normalize with absolute := true }
  let rewrittenTarget : RequestTarget :=
    if isCrossOrigin then
      .absoluteForm { target with path, authority := some { authority with userInfo := none }, fragment := none }
    else
      .originForm path target.query

  return .follow {
    origin := newOrigin
    target := rewrittenTarget
    method := newMethod
    headers := newHeaders
    bodyAction := bodyAction
    isCrossOrigin := isCrossOrigin
  }

end Std.Http.Protocol.H1

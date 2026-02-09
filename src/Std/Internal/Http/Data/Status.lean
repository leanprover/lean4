/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Internal

public section

/-!
# Status

This module defines the `Status` type, which is a representation of HTTP status codes. Status codes are three-digit
integer codes that describe the result of an HTTP request. In this implementation we do not treat status
code as extensible.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
HTTP Status codes. Status codes are three-digit integer codes that describe the result of an
HTTP request. In this implementation we do not treat status code as extensible.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
inductive Status where
  /--
  100 Continue
  -/
  | «continue»

  /--
  101 Switching Protocols
  -/
  | switchingProtocols

  /--
  102 Processing
  -/
  | processing

  /--
  103 Early Hints
  -/
  | earlyHints

  /--
  200 OK
  -/
  | ok

  /--
  201 Created
  -/
  | created

  /--
  202 Accepted
  -/
  | accepted

  /--
  203 Non-Authoritative Information
  -/
  | nonAuthoritativeInformation

  /--
  204 No Content
  -/
  | noContent

  /--
  205 Reset Content
  -/
  | resetContent

  /--
  206 Partial Content
  -/
  | partialContent

  /--
  207 Multi-Status
  -/
  | multiStatus

  /--
  208 Already Reported
  -/
  | alreadyReported

  /--
  226 IM Used
  -/
  | imUsed

  /--
  300 Multiple Choices
  -/
  | multipleChoices

  /--
  301 Moved Permanently
  -/
  | movedPermanently

  /--
  302 Found
  -/
  | found

  /--
  303 See Other
  -/
  | seeOther

  /--
  304 Not Modified
  -/
  | notModified

  /--
  305 Use Proxy
  -/
  | useProxy

  /--
  306 Unused
  -/
  | unused

  /--
  307 Temporary Redirect
  -/
  | temporaryRedirect

  /--
  308 Permanent Redirect
  -/
  | permanentRedirect

  /--
  400 Bad Request
  -/
  | badRequest

  /--
  401 Unauthorized
  -/
  | unauthorized

  /--
  402 Payment Required
  -/
  | paymentRequired

  /--
  403 Forbidden
  -/
  | forbidden

  /--
  404 Not Found
  -/
  | notFound

  /--
  405 Method Not Allowed
  -/
  | methodNotAllowed

  /--
  406 Not Acceptable
  -/
  | notAcceptable

  /--
  407 Proxy Authentication Required
  -/
  | proxyAuthenticationRequired

  /--
  408 Request Timeout
  -/
  | requestTimeout

  /--
  409 Conflict
  -/
  | conflict

  /--
  410 Gone
  -/
  | gone

  /--
  411 Length Required
  -/
  | lengthRequired

  /--
  412 Precondition Failed
  -/
  | preconditionFailed

  /--
  413 Payload Too Large
  -/
  | payloadTooLarge

  /--
  414 URI Too Long
  -/
  | uriTooLong

  /--
  415 Unsupported Media Type
  -/
  | unsupportedMediaType

  /--
  416 Range Not Satisfiable
  -/
  | rangeNotSatisfiable

  /--
  417 Expectation Failed
  -/
  | expectationFailed

  /--
  418 I'm a teapot
  -/
  | imATeapot

  /--
  421 Misdirected Request
  -/
  | misdirectedRequest

  /--
  422 Unprocessable Entity
  -/
  | unprocessableEntity

  /--
  423 Locked
  -/
  | locked

  /--
  424 Failed Dependency
  -/
  | failedDependency

  /--
  425 Too Early
  -/
  | tooEarly

  /--
  426 Upgrade Required
  -/
  | upgradeRequired

  /--
  428 Precondition Required
  -/
  | preconditionRequired

  /--
  429 Too Many Requests
  -/
  | tooManyRequests

  /--
  431 Request Header Fields Too Large
  -/
  | requestHeaderFieldsTooLarge

  /--
  451 Unavailable For Legal Reasons
  -/
  | unavailableForLegalReasons

  /--
  500 Internal Server Error
  -/
  | internalServerError

  /--
  501 Not Implemented
  -/
  | notImplemented

  /--
  502 Bad Gateway
  -/
  | badGateway

  /--
  503 Service Unavailable
  -/
  | serviceUnavailable

  /--
  504 Gateway Timeout
  -/
  | gatewayTimeout

  /--
  505 HTTP Version Not Supported
  -/
  | httpVersionNotSupported

  /--
  506 Variant Also Negotiates
  -/
  | variantAlsoNegotiates

  /--
  507 Insufficient Storage
  -/
  | insufficientStorage

  /--
  508 Loop Detected
  -/
  | loopDetected

  /--
  510 Not Extended
  -/
  | notExtended

  /--
  511 Network Authentication Required
  -/
  | networkAuthenticationRequired

  /--
  Other
  -/
  | other (number : UInt16)
deriving Repr, Inhabited, BEq

namespace Status

/--
Convert a Status to a numeric code. This is useful for sending the status code in a response.
-/
def toCode : Status → UInt16
  | «continue» => 100
  | switchingProtocols => 101
  | processing => 102
  | earlyHints => 103
  | ok => 200
  | created => 201
  | accepted => 202
  | nonAuthoritativeInformation => 203
  | noContent => 204
  | resetContent => 205
  | partialContent => 206
  | multiStatus => 207
  | alreadyReported => 208
  | imUsed => 226
  | multipleChoices => 300
  | movedPermanently => 301
  | found => 302
  | seeOther => 303
  | notModified => 304
  | useProxy => 305
  | unused => 306
  | temporaryRedirect => 307
  | permanentRedirect => 308
  | badRequest => 400
  | unauthorized => 401
  | paymentRequired => 402
  | forbidden => 403
  | notFound => 404
  | methodNotAllowed => 405
  | notAcceptable => 406
  | proxyAuthenticationRequired => 407
  | requestTimeout => 408
  | conflict => 409
  | gone => 410
  | lengthRequired => 411
  | preconditionFailed => 412
  | payloadTooLarge => 413
  | uriTooLong => 414
  | unsupportedMediaType => 415
  | rangeNotSatisfiable => 416
  | expectationFailed => 417
  | imATeapot => 418
  | misdirectedRequest => 421
  | unprocessableEntity => 422
  | locked => 423
  | failedDependency => 424
  | tooEarly => 425
  | upgradeRequired => 426
  | preconditionRequired => 428
  | tooManyRequests => 429
  | requestHeaderFieldsTooLarge => 431
  | unavailableForLegalReasons => 451
  | internalServerError => 500
  | notImplemented => 501
  | badGateway => 502
  | serviceUnavailable => 503
  | gatewayTimeout => 504
  | httpVersionNotSupported => 505
  | variantAlsoNegotiates => 506
  | insufficientStorage => 507
  | loopDetected => 508
  | notExtended => 510
  | networkAuthenticationRequired => 511
  | other n => n

/--
Converts a `UInt16` to `Status`.
-/
def ofCode : UInt16 → Status
  | 100 => .«continue»
  | 101 => .switchingProtocols
  | 102 => .processing
  | 103 => .earlyHints
  | 200 => .ok
  | 201 => .created
  | 202 => .accepted
  | 203 => .nonAuthoritativeInformation
  | 204 => .noContent
  | 205 => .resetContent
  | 206 => .partialContent
  | 207 => .multiStatus
  | 208 => .alreadyReported
  | 226 => .imUsed
  | 300 => .multipleChoices
  | 301 => .movedPermanently
  | 302 => .found
  | 303 => .seeOther
  | 304 => .notModified
  | 305 => .useProxy
  | 306 => .unused
  | 307 => .temporaryRedirect
  | 308 => .permanentRedirect
  | 400 => .badRequest
  | 401 => .unauthorized
  | 402 => .paymentRequired
  | 403 => .forbidden
  | 404 => .notFound
  | 405 => .methodNotAllowed
  | 406 => .notAcceptable
  | 407 => .proxyAuthenticationRequired
  | 408 => .requestTimeout
  | 409 => .conflict
  | 410 => .gone
  | 411 => .lengthRequired
  | 412 => .preconditionFailed
  | 413 => .payloadTooLarge
  | 414 => .uriTooLong
  | 415 => .unsupportedMediaType
  | 416 => .rangeNotSatisfiable
  | 417 => .expectationFailed
  | 418 => .imATeapot
  | 421 => .misdirectedRequest
  | 422 => .unprocessableEntity
  | 423 => .locked
  | 424 => .failedDependency
  | 425 => .tooEarly
  | 426 => .upgradeRequired
  | 428 => .preconditionRequired
  | 429 => .tooManyRequests
  | 431 => .requestHeaderFieldsTooLarge
  | 451 => .unavailableForLegalReasons
  | 500 => .internalServerError
  | 501 => .notImplemented
  | 502 => .badGateway
  | 503 => .serviceUnavailable
  | 504 => .gatewayTimeout
  | 505 => .httpVersionNotSupported
  | 506 => .variantAlsoNegotiates
  | 507 => .insufficientStorage
  | 508 => .loopDetected
  | 510 => .notExtended
  | 511 => .networkAuthenticationRequired
  | n => .other n

/--
Checks if the type of the status code is informational, meaning that the request was received
and the process is continuing.
-/
@[inline]
def isInformational (c : Status) : Bool :=
  100 ≤ c.toCode ∧ c.toCode < 200

/--
Checks if the type of the status code is success, meaning that the request was successfully received,
understood, and accepted.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isSuccess (c : Status) : Bool :=
  200 ≤ c.toCode ∧ c.toCode < 300

/--
Checks if the type of the status code is redirection, meaning that further action needs to be taken
to complete the request.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isRedirection (c : Status) : Bool :=
  300 ≤ c.toCode ∧ c.toCode < 400

/--
Checks if the type of the status code is a client error, meaning that the request contains bad syntax
or cannot be fulfilled.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isClientError (c : Status) : Bool :=
  400 ≤ c.toCode ∧ c.toCode < 500

/--
Checks if the type of the status code is a server error, meaning that the server failed to fulfill
an apparently valid request.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isServerError (c : Status) : Bool :=
  500 ≤ c.toCode ∧ c.toCode < 600

/--
Checks if the status code indicates an error (either client error 4xx or server error 5xx).

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isError (c : Status) : Bool :=
  c.isClientError ∨ c.isServerError

/--
Returns the standard reason phrase for an HTTP status code as defined in RFC 9110.
For known status codes this returns the canonical phrase (e.g., "OK" for 200).
For unknown codes (`other n`), returns the numeric code as a string.
-/
def reasonPhrase : Status → String
  | .«continue» => "Continue"
  | .switchingProtocols => "Switching Protocols"
  | .processing => "Processing"
  | .earlyHints => "Early Hints"
  | .ok => "OK"
  | .created => "Created"
  | .accepted => "Accepted"
  | .nonAuthoritativeInformation => "Non-Authoritative Information"
  | .noContent => "No Content"
  | .resetContent => "Reset Content"
  | .partialContent => "Partial Content"
  | .multiStatus => "Multi-Status"
  | .alreadyReported => "Already Reported"
  | .imUsed => "IM Used"
  | .multipleChoices => "Multiple Choices"
  | .movedPermanently => "Moved Permanently"
  | .found => "Found"
  | .seeOther => "See Other"
  | .notModified => "Not Modified"
  | .useProxy => "Use Proxy"
  | .unused => "Unused"
  | .temporaryRedirect => "Temporary Redirect"
  | .permanentRedirect => "Permanent Redirect"
  | .badRequest => "Bad Request"
  | .unauthorized => "Unauthorized"
  | .paymentRequired => "Payment Required"
  | .forbidden => "Forbidden"
  | .notFound => "Not Found"
  | .methodNotAllowed => "Method Not Allowed"
  | .notAcceptable => "Not Acceptable"
  | .proxyAuthenticationRequired => "Proxy Authentication Required"
  | .requestTimeout => "Request Timeout"
  | .conflict => "Conflict"
  | .gone => "Gone"
  | .lengthRequired => "Length Required"
  | .preconditionFailed => "Precondition Failed"
  | .payloadTooLarge => "Payload Too Large"
  | .uriTooLong => "URI Too Long"
  | .unsupportedMediaType => "Unsupported Media Type"
  | .rangeNotSatisfiable => "Range Not Satisfiable"
  | .expectationFailed => "Expectation Failed"
  | .imATeapot => "I'm a teapot"
  | .misdirectedRequest => "Misdirected Request"
  | .unprocessableEntity => "Unprocessable Entity"
  | .locked => "Locked"
  | .failedDependency => "Failed Dependency"
  | .tooEarly => "Too Early"
  | .upgradeRequired => "Upgrade Required"
  | .preconditionRequired => "Precondition Required"
  | .tooManyRequests => "Too Many Requests"
  | .requestHeaderFieldsTooLarge => "Request Header Fields Too Large"
  | .unavailableForLegalReasons => "Unavailable For Legal Reasons"
  | .internalServerError => "Internal Server Error"
  | .notImplemented => "Not Implemented"
  | .badGateway => "Bad Gateway"
  | .serviceUnavailable => "Service Unavailable"
  | .gatewayTimeout => "Gateway Timeout"
  | .httpVersionNotSupported => "HTTP Version Not Supported"
  | .variantAlsoNegotiates => "Variant Also Negotiates"
  | .insufficientStorage => "Insufficient Storage"
  | .loopDetected => "Loop Detected"
  | .notExtended => "Not Extended"
  | .networkAuthenticationRequired => "Network Authentication Required"
  | .other n => Nat.repr n.toNat

instance : ToString Status where
  toString := reasonPhrase

instance : Encode .v11 Status where
  encode buffer status := buffer
    |>.writeString (toString <| toCode status)
    |>.writeChar ' '
    |>.writeString status.reasonPhrase

end Std.Http.Status

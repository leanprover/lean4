/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Internal.Http.Encode

namespace Std
namespace Http
namespace Data

set_option linter.all true

/--
HTTP Status codes. Status codes are three-digit integer codes that describes the result of a
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
deriving Repr, Inhabited

instance : ToString Status where
  toString
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
    | .payloadTooLarge => "Request Entity Too Large"
    | .uriTooLong => "Request URI Too Long"
    | .unsupportedMediaType => "Unsupported Media Type"
    | .rangeNotSatisfiable => "Requested Range Not Satisfiable"
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

namespace Status

/--
Convert a Status to a numeric code. This is useful for sending the status code in a response.
-/
def toCode : Status -> UInt16
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

/--
Converts an `UInt16` to a `Status`.
-/
def fromCode? : UInt16 → Option Status
  | 100 => some «continue»
  | 101 => some switchingProtocols
  | 102 => some processing
  | 103 => some earlyHints
  | 200 => some ok
  | 201 => some created
  | 202 => some accepted
  | 203 => some nonAuthoritativeInformation
  | 204 => some noContent
  | 205 => some resetContent
  | 206 => some partialContent
  | 207 => some multiStatus
  | 208 => some alreadyReported
  | 226 => some imUsed
  | 300 => some multipleChoices
  | 301 => some movedPermanently
  | 302 => some found
  | 303 => some seeOther
  | 304 => some notModified
  | 305 => some useProxy
  | 306 => some unused
  | 307 => some temporaryRedirect
  | 308 => some permanentRedirect
  | 400 => some badRequest
  | 401 => some unauthorized
  | 402 => some paymentRequired
  | 403 => some forbidden
  | 404 => some notFound
  | 405 => some methodNotAllowed
  | 406 => some notAcceptable
  | 407 => some proxyAuthenticationRequired
  | 408 => some requestTimeout
  | 409 => some conflict
  | 410 => some gone
  | 411 => some lengthRequired
  | 412 => some preconditionFailed
  | 413 => some payloadTooLarge
  | 414 => some uriTooLong
  | 415 => some unsupportedMediaType
  | 416 => some rangeNotSatisfiable
  | 417 => some expectationFailed
  | 418 => some imATeapot
  | 421 => some misdirectedRequest
  | 422 => some unprocessableEntity
  | 423 => some locked
  | 424 => some failedDependency
  | 425 => some tooEarly
  | 426 => some upgradeRequired
  | 428 => some preconditionRequired
  | 429 => some tooManyRequests
  | 431 => some requestHeaderFieldsTooLarge
  | 451 => some unavailableForLegalReasons
  | 500 => some internalServerError
  | 501 => some notImplemented
  | 502 => some badGateway
  | 503 => some serviceUnavailable
  | 504 => some gatewayTimeout
  | 505 => some httpVersionNotSupported
  | 506 => some variantAlsoNegotiates
  | 507 => some insufficientStorage
  | 508 => some loopDetected
  | 510 => some notExtended
  | 511 => some networkAuthenticationRequired
  | _   => none

/--
Checks if the type of the status code is informational, meaning that the request was received
and the process is continuing.
-/
@[inline]
def isInformational (c : Status) : Prop :=
  c.toCode < 200

/--
Checks if the type of the status code is success, meaning that the request was successfully received,
understood, and accepted.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isSuccess (c : Status) : Prop :=
  200 ≤ c.toCode ∧ c.toCode < 300

/--
Checks if the type of the status code is redirection, meaning that further action needs to be taken
to complete the request.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isRedirection (c : Status) : Prop :=
  300 ≤ c.toCode ∧ c.toCode < 400

/--
Checks if the type of the status code is a client error, meaning that the request contains bad syntax
or cannot be fulfilled.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isClientError (c : Status) : Prop :=
  400 ≤ c.toCode ∧ c.toCode < 500

/--
Checks if the type of the status code is a server error, meaning that the server failed to fulfill
an apparently valid request.

* Reference: https://httpwg.org/specs/rfc9110.html#status.codes
-/
@[inline]
def isServerError (c : Status) : Prop :=
  500 ≤ c.toCode ∧ c.toCode < 600

instance : Encode .v11 Status where
  encode buffer status := buffer
    |>.writeString (toString <| toCode status)
    |>.writeChar ' '
    |>.writeString (toString status)

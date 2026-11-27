import Std.Http

/-!
Tests the HTTP client configuration: the defaults of `Client.Config` (no proxy, authenticator or
cookie handler), `RequestOverrides.apply`, and `Config.toH1Config` with the field names the server's
`Config` uses.
-/

open Std.Http Std.Http.Client Std.Async

def origin (url : String) : URI.Origin :=
  (URI.parse! url).origin?.getD { scheme := URI.Scheme.ofString! "http", host := .empty, port := 0 }

def example80 : URI.Origin := origin "http://example.com"

def target : RequestTarget := RequestTarget.parse! "/"

/-! ## Defaults -/

#guard ({} : Client.Config).proxySelector.select example80 == Proxy.direct
#guard ({} : Client.Config).authenticator.isNone
#guard ({} : Client.Config).cookieHandler.isNone
#guard ({} : Client.Config).maxResponseBodySize.isNone

/-! ## `RequestOverrides` -/

-- A field left `none` keeps the configured value; a set one replaces it.
#guard
  let config : Client.Config := { maxRedirects := 3 }
  ({} : RequestOverrides).apply config |>.maxRedirects == 3
#guard
  let config : Client.Config := { maxRedirects := 3 }
  ({ maxRedirects := some 0 } : RequestOverrides).apply config |>.maxRedirects == 0
#guard
  let overrides : RequestOverrides := { requestTimeout := some ⟨500, by decide⟩ }
  (overrides.apply {}).requestTimeout.val == 500 && (({} : RequestOverrides).apply {}).requestTimeout.val == 120000

/-! ## `toH1Config` -/

-- The limits shared with the server go to the machine under the same names.
#guard
  let config : Client.Config :=
    { maxRequests := 7, maxHeaders := 9, maxHeaderNameLength := 11, maxHeaderValueLength := 13,
      enableKeepAlive := false, maxBufferedBodyBytes := 17 }
  let h1 := config.toH1Config
  h1.maxMessages == 7 && h1.maxHeaders == 9 && h1.maxHeaderNameLength == 11 &&
    h1.maxHeaderValueLength == 13 && !h1.enableKeepAlive && h1.maxBufferedBodyBytes == some 17

-- The header block allows `maxHeaders` lines at the longest name and value, so no response inside
-- all three limits is refused for its total size.
#guard
  let config : Client.Config := { maxHeaders := 2, maxHeaderNameLength := 10, maxHeaderValueLength := 20 }
  config.headerBlockSize == 2 * (10 + 20 + 4) && config.toH1Config.maxHeaderBytes == 68

-- A response body has no length limit in the machine: `maxResponseBodySize` bounds it instead.
#guard ({} : Client.Config).toH1Config.maxBodySize == 2 ^ 64

#guard ({} : Client.Config).toH1Config.agentName == some (.mk "lean-http/1.1")

import Std.Internal.Http.Data.Headers

open Std Http

-- ============================================================================
-- Headers.merge tests
-- ============================================================================

/--
info: 2
-/
#guard_msgs in
#eval do
  -- Merge with overlapping keys - multimap behavior keeps both values
  let h1 := Headers.empty.insert (.ofString! "content-type") (.ofString! "text/plain")
  let h2 := Headers.empty.insert (.ofString! "content-type") (.ofString! "application/json")
  let merged := h1.merge h2
  -- After merge, content-type should have both values
  IO.println (merged.getAll? (.ofString! "content-type")).get!.size

/--
info: 3
-/
#guard_msgs in
#eval do
  -- Merge with non-overlapping keys
  let h1 := Headers.empty.insert (.ofString! "x-custom-1") (.ofString! "value1")
  let h2 := Headers.empty
    |>.insert (.ofString! "x-custom-2") (.ofString! "value2")
    |>.insert (.ofString! "x-custom-3") (.ofString! "value3")
  let merged := h1.merge h2
  IO.println merged.size

-- ============================================================================
-- Headers.getAll tests (multi-value headers)
-- ============================================================================

/--
info: 3
-/
#guard_msgs in
#eval do
  -- Multiple values for same header
  let headers := Headers.empty
    |>.insert (.ofString! "accept") (.ofString! "text/html")
    |>.insert (.ofString! "accept") (.ofString! "application/json")
    |>.insert (.ofString! "accept") (.ofString! "text/plain")
  if let some values := headers.getAll? (.ofString! "accept") then
    IO.println values.size
  else
    IO.println "not found"

-- ============================================================================
-- Case-insensitive header lookup
-- ============================================================================

#guard
  let headers := Headers.empty.insert (.ofString! "content-type") (.ofString! "text/plain")
  -- All these should find the same header (case-insensitive)
  headers.contains (.ofString! "content-type") &&
  headers.contains (.ofString! "Content-Type") &&
  headers.contains (.ofString! "CONTENT-TYPE")

/--
info: text/plain
-/
#guard_msgs in
#eval do
  let headers := Headers.empty.insert (.ofString! "Content-Type") (.ofString! "text/plain")
  if let some v := headers.get? (.ofString! "content-type") then
    IO.println v.value
  else
    IO.println "not found"

-- ============================================================================
-- Invalid header name characters
-- ============================================================================

#guard (Header.Name.ofString? "valid-name").isSome
#guard (Header.Name.ofString? "").isNone  -- empty
#guard (Header.Name.ofString? "has space").isNone  -- space invalid
#guard (Header.Name.ofString? "has(paren").isNone  -- parentheses invalid
#guard (Header.Name.ofString? "has,comma").isNone  -- comma invalid

-- ============================================================================
-- Header value validation
-- ============================================================================

#guard (Header.Value.ofString? "valid value").isSome
#guard (Header.Value.ofString? "value with tab\t").isSome  -- tab is valid

-- ============================================================================
-- HasAll proofs
-- ============================================================================

/--
info: true
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert (.ofString! "content-type") (.ofString! "application/json")
    |>.insert (.ofString! "host") (.ofString! "example.com")
    |>.insert (.ofString! "accept") (.ofString! "text/plain")

  -- Check HasAll for a subset of headers
  let hasAll : Bool := match Headers.HasAll.decidable (h := headers) (l := ["content-type", "host"]) with
    | isTrue _ => true
    | isFalse _ => false
  IO.println hasAll

/--
info: false
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert (.ofString! "content-type") (.ofString! "application/json")

  -- Check HasAll for headers not present
  let hasAll : Bool := match Headers.HasAll.decidable (h := headers) (l := ["content-type", "missing-header"]) with
    | isTrue _ => true
    | isFalse _ => false
  IO.println hasAll

-- ============================================================================
-- Headers iteration (toArray, toList)
-- ============================================================================

/--
info: 2
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert (.ofString! "a") (.ofString! "1")
    |>.insert (.ofString! "b") (.ofString! "2")
  IO.println headers.toArray.size

/--
info: 2
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert (.ofString! "x") (.ofString! "y")
    |>.insert (.ofString! "z") (.ofString! "w")
  IO.println headers.toList.length

-- ============================================================================
-- Header name constants
-- ============================================================================

#guard Header.Name.contentType == .ofString! "content-type"
#guard Header.Name.contentLength == .ofString! "content-length"
#guard Header.Name.host == .ofString! "host"
#guard Header.Name.authorization == .ofString! "authorization"
#guard Header.Name.userAgent == .ofString! "user-agent"
#guard Header.Name.accept == .ofString! "accept"
#guard Header.Name.connection == .ofString! "connection"
#guard Header.Name.transferEncoding == .ofString! "transfer-encoding"

-- ============================================================================
-- Using header name constants in practice
-- ============================================================================

/--
info: application/json
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert Header.Name.contentType (.ofString! "application/json")
  if let some v := headers.get? Header.Name.contentType then
    IO.println v.value
  else
    IO.println "not found"

-- ============================================================================
-- Headers filter and map
-- ============================================================================

/--
info: 1
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert (.ofString! "x-custom") (.ofString! "keep")
    |>.insert (.ofString! "x-remove") (.ofString! "remove")
  let filtered := headers.filter (fun name _ => name.is "x-custom")
  IO.println filtered.size

-- ============================================================================
-- Headers update
-- ============================================================================

/--
info: updated
-/
#guard_msgs in
#eval do
  let headers := Headers.empty
    |>.insert (.ofString! "x-value") (.ofString! "original")
  let updated := headers.update (.ofString! "x-value") (fun _ => .ofString! "updated")
  if let some v := updated.get? (.ofString! "x-value") then
    IO.println v.value
  else
    IO.println "not found"

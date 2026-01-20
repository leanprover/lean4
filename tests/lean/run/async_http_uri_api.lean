/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Internal.Http.Data.URI

open Std.Http

/-!
# URI API Tests

Tests for Path utilities, URI modification helpers, normalization, and resolution.
-/

-- ============================================================================
-- Path.normalize tests (RFC 3986 Section 5.2.4)
-- ============================================================================

-- Single dot removal
/--
info: /a/b
-/
#guard_msgs in
#eval IO.println <| toString (URI.parse! "http://example.com/a/./b").path.normalize

-- Double dot removal
/--
info: /a
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/..").path.normalize

-- Complex path normalization
/--
info: /a/g
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/c/./../../g").path.normalize

-- Double dot at start (should not go above root)
/--
info: /g
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/../../../g").path.normalize

-- Mixed dots
/--
info: /a/c
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/../c").path.normalize

-- Multiple consecutive dots and double-dots
/--
info: /a/
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/c/../.././").path.normalize

-- ============================================================================
-- Path.parent tests
-- ============================================================================

/--
info: /a/b
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/c").path.parent

/--
info: /a
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b").path.parent

/--
info: /
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a").path.parent

-- Parent of root path
/--
info: /
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/").path.parent

-- ============================================================================
-- Path.join tests
-- ============================================================================

/--
info: /a/b/c/d
-/
#guard_msgs in
#eval do
  let p1 := (URI.parse! "http://example.com/a/b").path
  let p2 : URI.Path := { segments := #[URI.EncodedString.encode "c", URI.EncodedString.encode "d"], absolute := false }
  IO.println (p1.join p2)

-- Join with absolute path (absolute path wins)
/--
info: /x/y
-/
#guard_msgs in
#eval do
  let p1 := (URI.parse! "http://example.com/a/b").path
  let p2 : URI.Path := { segments := #[URI.EncodedString.encode "x", URI.EncodedString.encode "y"], absolute := true }
  IO.println (p1.join p2)

-- ============================================================================
-- Path.isEmpty tests
-- ============================================================================

#guard (URI.parse! "http://example.com").path.isEmpty = true
#guard (URI.parse! "http://example.com/").path.absolute = true
#guard (URI.parse! "http://example.com/a").path.isEmpty = false
#guard (URI.parse! "http://example.com/a").path.absolute = true

-- ============================================================================
-- URI modification helpers tests
-- ============================================================================

-- withScheme
#guard ((URI.parse! "http://example.com").withScheme "htTps" |>.scheme) == "https"
#guard ((URI.parse! "http://example.com").withScheme "ftP" |>.scheme) == "ftp"

-- withFragment
/--
info: http://example.com/#section1
-/
#guard_msgs in
#eval IO.println ((URI.parse! "http://example.com/").withFragment (some (toString <| URI.EncodedString.encode "section1")))

-- withQuery
/--
info: http://example.com/?key=value
-/
#guard_msgs in
#eval do
  let uri := URI.parse! "http://example.com/"
  let query := URI.Query.empty.insert "key" "value"
  IO.println (uri.withQuery query)

-- withPath
/--
info: http://example.com/new/path
-/
#guard_msgs in
#eval do
  let uri := URI.parse! "http://example.com/old/path"
  let newPath : URI.Path := { segments := #[URI.EncodedString.encode "new", URI.EncodedString.encode "path"], absolute := true }
  IO.println (uri.withPath newPath)

-- ============================================================================
-- URI.normalize tests (RFC 3986 Section 6)
-- ============================================================================

-- Scheme normalization (lowercase)
#guard (URI.parse! "HTTP://example.com").normalize.scheme == "http"
#guard (URI.parse! "HtTpS://example.com").normalize.scheme == "https"

-- Host normalization (lowercase)
/--
info: http://example.com/
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://EXAMPLE.COM/").normalize

/--
info: http://example.com/
-/
#guard_msgs in
#eval IO.println (URI.parse! "HTTP://Example.COM/").normalize

-- Path normalization (dot removal)
/--
info: http://example.com/a/c
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/../c").normalize

-- Combined normalization
/--
info: http://example.com/a/g
-/
#guard_msgs in
#eval IO.println (URI.parse! "HTTP://EXAMPLE.COM/a/b/c/./../../g").normalize

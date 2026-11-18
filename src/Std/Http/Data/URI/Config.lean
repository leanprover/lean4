/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Nat.Basic

public section

/-!
# URI Parser Configuration

This module defines `URI.Config`, which controls per-component size limits used during URI
parsing. All limits default to the values previously hardcoded in the parser, except
`maxQueryLength`, which is raised from 1024 to 8192 to match `H1.Config.maxUriLength` and
accommodate real-world query strings.
-/

namespace Std.Http.URI

set_option linter.all true

/--
Per-component size limits for the URI parser. The defaults bound a URI by its total path and query
lengths; the component limits below them only reject what those already would, except the host's,
which is the length of a DNS name.
-/
structure Config where
  /--
  Maximum length of the URI scheme component (e.g. `https`), in bytes.
  The scheme grammar requires at least one leading ALPHA; the remaining budget is
  `max(0, maxSchemeLength - 1)` additional characters.
  -/
  maxSchemeLength : Nat := 64

  /--
  Maximum length of the host `reg-name` component after percent-decoding, in bytes, not counting
  the trailing `.` of a fully qualified name.
  -/
  maxHostLength : Nat := 253

  /--
  Maximum length of the userinfo component (username and password each), in bytes.
  -/
  maxUserInfoLength : Nat := 1024

  /--
  Maximum length of a single path segment, in bytes.
  -/
  maxSegmentLength : Nat := 8192

  /--
  Maximum length of the query string, in bytes.
  Raised from the previously hardcoded 1024 to 8192 to match `H1.Config.maxUriLength`
  and allow real-world query strings.
  -/
  maxQueryLength : Nat := 8192

  /--
  Maximum length of the fragment component, in bytes.
  -/
  maxFragmentLength : Nat := 8192

  /--
  Maximum number of path segments.
  Prevents excessive segment counts that could arise from paths like `/a/b/c/…` repeated many times.
  -/
  maxPathSegments : Nat := 8192

  /--
  Maximum total byte length of the path (all segments combined, including separating slashes).
  -/
  maxTotalPathLength : Nat := 8192

  /--
  Maximum number of query parameters (key-value pairs separated by `&`).
  -/
  maxQueryParams : Nat := 8192

end Std.Http.URI

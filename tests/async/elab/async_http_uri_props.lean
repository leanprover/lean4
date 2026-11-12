module

import Std.Http.Test.Helpers

/-!
# URI printing properties

Generated checks that printing a URI or a reference and parsing it again keeps its authority and,
once dot segments are removed, its path. RFC 3986 §3.3, §4.2.
-/

open Std Http
open Std.Http.Internal.Test

private def relRef? (s : String) : Option URI.RelativeRef :=
  match URIReference.parse? s with
  | some (.relative r) => some r
  | _ => none

private def mkPath (segments : List String) (absolute : Bool) : URI.Path :=
  { segments := (segments.map URI.EncodedSegment.encode).toArray, absolute }

private def segmentLists (shapes : List String) : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => [] :: shapes.flatMap fun s => (segmentLists shapes n).map (s :: ·)

/-! ## Print-parse round-trip property -/

-- Every path over a few segment shapes, in a URI and in a reference, with and without an authority,
-- prints as a string that reads back with the same authority and, once dot segments are removed,
-- the same path.
#eval checkCases "Printing reads back as the same components" #[
    ("segments over \"\", \".\", \"..\", \"a\", \"a:b\" up to depth 3", do
      let authorities : List (Option URI.Authority) :=
        [none, (URI.parse! "foo://host").authority]
      let render (path : URI.Path) (authority : Option URI.Authority) (scheme : Bool) : String :=
        path.normalize.render authority.isSome scheme
      for segments in segmentLists ["", ".", "..", "a", "a:b"] 3 do
        for absolute in [false, true] do
          let path := mkPath segments absolute
          for authority in authorities do
            -- After an authority a non-empty path can only be absolute.
            let meant :=
              if authority.isSome && !(toString path).isEmpty then { path with absolute := true } else path
            let uri : URI :=
              { scheme := URI.Scheme.ofString! "foo", authority, path, query := none, fragment := none }
            match URI.parse? (toString uri) with
            | some back =>
              unless back.authority == authority && render back.path authority true == render meant authority true do
                throw <| IO.userError s!"URI {repr path} printed as {toString uri} reads back as {repr back}"
            | none => throw <| IO.userError s!"URI {repr path} printed as {toString uri} does not parse"
            let ref : URI.RelativeRef := { authority, path, fragment := none }
            match relRef? (toString ref) with
            | some back =>
              unless back.authority == authority && render back.path authority false == render meant authority false do
                throw <| IO.userError s!"reference {repr path} printed as {toString ref} reads back as {repr back}"
            | none => throw <| IO.userError s!"reference {repr path} printed as {toString ref} does not parse")
  ] (·.2)

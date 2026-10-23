module
meta import Std.Http.Data.URI

/-!
Regression tests for #15246: literal `+` characters in form-encoded query keys and values.
Encoding must distinguish a literal plus from a space, including through query updates and URI builders.
-/

open Std.Http URI

#guard toString (EncodedQueryString.encode "+ +") == "%2B+%2B"
#guard toString (EncodedQueryParam.encode "+ +") == "%2B+%2B"
#guard toString (EncodedQueryString.encode "+" (fun _ => true)) == "%2B"
#guard toString (EncodedQueryString.encode "+" (fun _ => false)) == "%2B"

#guard (["", "+", " ", "a+b", "a b", "%2B", "++ +%&=", "中文+é 🙂"] : List String).all fun s =>
  (EncodedQueryString.encode s).decode == some s &&
  (EncodedQueryParam.encode s).decode == some s

#guard (List.range 128).all fun n =>
  let c := String.singleton (Char.ofNat n)
  let s := c ++ "+" ++ c
  (EncodedQueryString.encode s).decode == some s &&
  (EncodedQueryParam.encode s).decode == some s

-- Already encoded input retains form decoding, while non-query components retain literal pluses.
#guard (EncodedQueryParam.fromString? "+").bind EncodedQueryParam.decode == some " "
#guard (EncodedQueryParam.fromString? "%2B%2b").bind EncodedQueryParam.decode == some "++"
#guard toString (EncodedSegment.encode "+") == "+"
#guard (EncodedSegment.encode "+").decode == some "+"
#guard toString (EncodedFragment.encode "+") == "+"
#guard toString (EncodedUserInfo.encode "+") == "+"

private meta def sampleQuery : Query :=
  Query.empty
    |>.insert "a+b" "x+y"
    |>.insert "a b" "x y"
    |>.insert "a%2Bb" "%2B"

#guard sampleQuery.toRawString == "a%2Bb=x%2By&a+b=x+y&a%252Bb=%252B"
#guard sampleQuery.get "a+b" == some "x+y"
#guard sampleQuery.get "a b" == some "x y"
#guard sampleQuery.get "a%2Bb" == some "%2B"
#guard !(Query.empty.insert "a+b" "value").contains "a b"
#guard ((sampleQuery.insert "a+b" "+").findAll "a+b").map (·.bind EncodedQueryParam.decode) ==
  #[some "x+y", some "+"]

#guard
  let erased := sampleQuery.erase "a+b"
  !erased.contains "a+b" && erased.get "a b" == some "x y" &&
    erased.get "a%2Bb" == some "%2B"

#guard
  let updated := sampleQuery.set "a+b" "+"
  updated.get "a+b" == some "+" && updated.get "a b" == some "x y" &&
    updated.get "a%2Bb" == some "%2B" && (updated.findAll "a+b").size == 1

#guard
  match (Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run
      s!"/path?{sampleQuery.toRawString}".toUTF8 with
  | .ok target => target.query == sampleQuery && target.query.get "a+b" == some "x+y"
  | .error _ => false

#guard
  match (Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run
      "/path?a%2Bb=x%2By&a+b=x+y".toUTF8 with
  | .ok target => target.query.get "a+b" == some "x+y" && target.query.get "a b" == some "x y"
  | .error _ => false

#guard
  let uri := Builder.empty
    |>.setHost! "example.com"
    |>.appendPathSegment "a+b"
    |>.addQueryParam "a+b" "x+y"
    |>.addQueryParam "a b" "x y"
    |>.addQueryFlag "+"
    |>.build
  toString uri == "https://example.com/a+b?a%2Bb=x%2By&a+b=x+y&%2B" &&
    (uri.query.bind (·.get "a+b")) == some "x+y" &&
    (uri.query.bind (·.get "+")) == some ""

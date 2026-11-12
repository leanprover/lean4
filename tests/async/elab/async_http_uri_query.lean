module

import Std.Http.Test.Helpers
import Std.Http.Data.URI.Encoding

/-!
# URI queries

Form encoding of query strings (a literal `+` versus a space), and how `URI.Query` looks names up,
updates, prints and splits a query. RFC 3986 §3.4. Regressions: #14934, #15246, #15892, #16021.
-/

open Std Http
open Std.Http.URI
open Std.Http.URI.Parser
open Std.Http.Internal.Test

private def target? (s : String) : Option RequestTarget :=
  ((parseRequestTarget <* Std.Internal.Parsec.eof).run s.toUTF8).toOption

/-- The query of the origin-form target `s`; fails if `s` does not parse. -/
private def queryOf (s : String) : IO URI.Query :=
  match target? s with
  | some t => pure t.query
  | none => throw <| IO.userError s!"{s.quote} did not parse"

private def sampleQuery : Query :=
  Query.empty
    |>.insert "a+b" "x+y"
    |>.insert "a b" "x y"
    |>.insert "a%2Bb" "%2B"

/-! ## Form encoding (#15246) -/

#eval checkCases "Query String Encoding Tests" #[
    ("ofByteArray? hello+world", expectEq "ofByteArray?"
      (reprLine (EncodedQueryString.ofByteArray? "hello+world".toUTF8)) "some \"hello+world\""),
    ("ofByteArray? %", expectEq "ofByteArray?" (reprLine (EncodedQueryString.ofByteArray? "%".toUTF8)) "none"),
    ("decode hello+world", expectEq "decode"
      (reprLine (EncodedQueryString.decode =<< EncodedQueryString.ofByteArray? "hello+world".toUTF8))
      "some \"hello world\""),
    ("decode %20", expectEq "decode"
      (reprLine (EncodedQueryString.decode =<< EncodedQueryString.ofByteArray? "%20".toUTF8)) "some \" \""),
    ("EncodedQueryString.encode \"+ +\"", expectEq "encode" (toString (EncodedQueryString.encode "+ +")) "%2B+%2B"),
    ("EncodedQueryParam.encode \"+ +\"", expectEq "encode" (toString (EncodedQueryParam.encode "+ +")) "%2B+%2B"),
    ("encode \"+\" with an always-true predicate",
      expectEq "encode" (toString (EncodedQueryString.encode "+" (fun _ => true))) "%2B"),
    ("encode \"+\" with an always-false predicate",
      expectEq "encode" (toString (EncodedQueryString.encode "+" (fun _ => false))) "%2B")
  ] (·.2)

#eval checkCases "encode then decode returns the input, for both query types" #[
    "",
    "+",
    " ",
    "a+b",
    "a b",
    "%2B",
    "++ +%&=",
    "中文+é 🙂"
  ] fun s => do
    expectEq "EncodedQueryString" (EncodedQueryString.encode s).decode (some s)
    expectEq "EncodedQueryParam" (EncodedQueryParam.encode s).decode (some s)

#eval checkCases "Already encoded input retains form decoding" #[
    ("c ++ \"+\" ++ c round-trips for every ASCII c", do
      for n in List.range 128 do
        let c := String.singleton (Char.ofNat n)
        let s := c ++ "+" ++ c
        expectEq "EncodedQueryString" (EncodedQueryString.encode s).decode (some s)
        expectEq "EncodedQueryParam" (EncodedQueryParam.encode s).decode (some s)),
    ("fromString? +", expectEq "decode" ((EncodedQueryParam.fromString? "+").bind EncodedQueryParam.decode)
      (some " ")),
    ("fromString? %2B%2b", expectEq "decode"
      ((EncodedQueryParam.fromString? "%2B%2b").bind EncodedQueryParam.decode) (some "++"))
  ] (·.2)

/-! ## Lookups -/

private def browserQuery : URI.Query :=
  match EncodedQueryParam.fromString? "a%3Ab", EncodedQueryParam.fromString? "on" with
  | some k, some v => URI.Query.empty.insertEncoded k (some v)
  | _, _ => URI.Query.empty

private def encodedA : IO EncodedQueryParam :=
  match EncodedQueryParam.fromString? "%61" with
  | some a => pure a
  | none => throw <| IO.userError "%61 is not a valid query name"

#eval checkCases "Query Parameter Tests" #[
    ("Query with duplicate keys: findAll size", do
      expectEq "findAll" ((← queryOf "/search?tag=a&tag=b&tag=c").findAll "tag").size 3),
    ("Query with duplicate keys: findAll values", do
      expectEq "findAll" (reprLine ((← queryOf "/search?tag=a&tag=b&tag=c").findAll "tag"))
        "#[some \"a\", some \"b\", some \"c\"]"),
    ("Query with duplicate keys: find? is the first", do
      expectEq "find?" (reprLine ((← queryOf "/search?key=a&key=b&key=c").find? "key")) "some (some \"a\")"),
    ("Empty value vs no value: key=", do
      expectEq "find?" (reprLine ((← queryOf "/api?key=").find? "key")) "some (some \"\")"),
    ("Empty value vs no value: key", do
      expectEq "find?" (reprLine ((← queryOf "/api?key").find? "key")) "some none"),
    ("Empty value vs no value: key=value", do
      expectEq "find?" (reprLine ((← queryOf "/api?key=value").find? "key")) "some (some \"value\")")
  ] (·.2)

-- `String`-keyed lookups match every spelling of a name; `*Encoded` lookups match exact bytes.
#eval checkCases "`String`-keyed and `*Encoded` lookups (#15892)" #[
    ("find? decodes", do
      let q ← queryOf "/api?%61=1&a=2"
      expectEq "find? a" ((q.find? "a").bind id |>.bind EncodedQueryParam.decode) (some "1")),
    ("findAll matches both spellings", do
      expectEq "findAll a" ((← queryOf "/api?%61=1&a=2").findAll "a").size 2),
    ("find? by the encoded spelling", do
      ensure ((← queryOf "/api?%61=1&a=2").find? "%61").isNone "find? %61"),
    ("contains", do ensure ((← queryOf "/api?%61=1&a=2").contains "a") "contains a"),
    ("contains by the encoded spelling", do
      ensure (!(← queryOf "/api?%61=1&a=2").contains "%61") "contains %61"),
    ("findEncoded?", do
      let q ← queryOf "/api?%61=1&a=2"
      expectEq "findEncoded? %61" ((q.findEncoded? (← encodedA)).bind id |>.bind EncodedQueryParam.decode)
        (some "1")),
    ("containsEncoded", do
      ensure ((← queryOf "/api?%61=1&a=2").containsEncoded (← encodedA)) "containsEncoded %61"),
    ("erase removes both spellings", do
      let erased := (← queryOf "/api?%61=1&a=2").erase "a"
      ensure (!erased.contains "a") "erase a: contains a"
      ensure (!erased.containsEncoded (← encodedA)) "erase a: containsEncoded %61"),
    ("eraseEncoded removes only the exact bytes", do
      let erased := (← queryOf "/api?%61=1&a=2").eraseEncoded (← encodedA)
      ensure (!erased.containsEncoded (← encodedA)) "eraseEncoded %61: containsEncoded %61"
      ensure (erased.contains "a") "eraseEncoded %61: contains a")
  ] (·.2)

-- #14934: a name a browser percent-encodes is found by its decoded spelling.
#eval checkCases "Query Operations (#14934)" #[
    ("get", expectEq "get" (browserQuery.get "a:b") (some "on")),
    ("getD", expectEq "getD" (browserQuery.getD "a:b" "off") "on"),
    ("contains", ensure (browserQuery.contains "a:b") "contains a:b"),
    ("findAll", expectEq "findAll" (browserQuery.findAll "a:b").size 1),
    ("contains by the encoded spelling", ensure (!browserQuery.contains "a%3Ab") "contains a%3Ab"),
    ("erase", ensure (browserQuery.erase "a:b").isEmpty "erase a:b"),
    ("set", expectEq "set" (toString (browserQuery.set "a:b" "off")) "?a:b=off"),
    ("parseRequestTarget", do
      expectEq "get" ((← queryOf "/consent?a%3Ab=on").get "a:b") (some "on")),
    ("URI.parse?", expectEq "get"
      ((URI.parse? "https://example.com/consent?a%3Ab=on").bind (·.query.bind (·.get "a:b"))) (some "on"))
  ] (·.2)

#eval checkCases "Lookups by decoded name (#15246)" #[
    ("get a+b", expectEq "get" (sampleQuery.get "a+b") (some "x+y")),
    ("get a b", expectEq "get" (sampleQuery.get "a b") (some "x y")),
    ("get a%2Bb", expectEq "get" (sampleQuery.get "a%2Bb") (some "%2B")),
    ("a+b is not a b", ensure (!(Query.empty.insert "a+b" "value").contains "a b") "contains a b"),
    ("findAll after inserting a+b again", expectEq "findAll"
      (((sampleQuery.insert "a+b" "+").findAll "a+b").map (·.bind EncodedQueryParam.decode))
      #[some "x+y", some "+"]),
    ("received a%2Bb and a+b", do
      let q ← queryOf "/path?a%2Bb=x%2By&a+b=x+y"
      ensure (q.get "a+b" == some "x+y" && q.get "a b" == some "x y") "get"),
    ("A raw plus in a received query name denotes a space, not a literal plus", do
      let q ← queryOf "/path?a+b=1"
      ensure (q.get "a b" == some "1" && q.get "a+b" == none) "get")
  ] (·.2)

#eval checkCases "`URI.Query.names`" #[
    ("unique names in order of first occurrence", do
      let names := (RequestTarget.parse! "/?b=1&a&b=2&c=&a=3&%61").query.names.map toString
      ensure (names == #["b", "a", "c", "%61"]) s!"names {names}"),
    -- A quadratic deduplication takes seconds here; a linear one, milliseconds.
    ("40000 distinct names", do
      let n := 40000
      let query := (List.range n).foldl (fun q i => q.insert s!"k{i}" "v") URI.Query.empty
      let start ← IO.monoMsNow
      let names ← IO.lazyPure fun _ => query.names
      -- Checked before the clock is read again, so the names are computed in between.
      ensure (names.size == n) s!"{names.size} names"
      let elapsed := (← IO.monoMsNow) - start
      ensure (elapsed < 2000) s!"Query.names took {elapsed} ms for {n} distinct names")
  ] (·.2)

-- `String`-keyed lookups compare a name as it decodes, byte by byte without decoding it into a new
-- string; this must agree with decoding and comparing.
#eval checkCases "`String`-keyed lookups agree with decoding and comparing" #[
    ("a%3Ab", "a%3Ab", "a:b"),
    ("a%3ab", "a%3ab", "a:b"),
    ("a+b as a b", "a+b", "a b"),
    ("a%2Bb", "a%2Bb", "a+b"),
    ("a+b as a+b", "a+b", "a+b"),
    ("abc", "abc", "abc"),
    ("abc as ab", "abc", "ab"),
    ("ab as abc", "ab", "abc"),
    ("%41 as A", "%41", "A"),
    ("%41 as a", "%41", "a"),
    ("r%C3%A9sum%C3%A9", "r%C3%A9sum%C3%A9", "résumé"),
    ("%E9", "%E9", "é"),
    ("%C3", "%C3", "Ã"),
    ("empty", "", ""),
    ("x as empty", "x", "")
  ] fun (_, enc, key) => do
    let some name := URI.EncodedQueryParam.ofByteArray? enc.toUTF8
      | throw (IO.userError s!"{enc} is not a valid query name")
    let query := (RequestTarget.parse! s!"/?{enc}=v").query
    let expected := name.decode == some key
    ensure (query.contains key == expected) s!"contains {key.quote} on {enc}: expected {expected}"
    ensure ((query.get key).isSome == expected) s!"get {key.quote} on {enc}: expected {expected}"

/-! ## Updates and printing -/

#eval checkCases "`&` and `=` in a name or value are percent-encoded" #[
    ("`&` in a key", expectEq "toRawString" (URI.Query.empty.insert "a&b" "1").toRawString "a%26b=1"),
    ("`=` in a key", expectEq "toRawString" (URI.Query.empty.insert "a=b" "1").toRawString "a%3Db=1"),
    ("`&` in a value", expectEq "toRawString" (URI.Query.empty.insert "key" "a&b").toRawString "key=a%26b"),
    ("`=` in a value", expectEq "toRawString" (URI.Query.empty.insert "key" "a=b").toRawString "key=a%3Db"),
    ("EncodedQueryParam.encode a=b", expectEq "encode" (toString (URI.EncodedQueryParam.encode "a=b")) "a%3Db")
  ] (·.2)

#eval checkCases "Print, then parse again" #[
    ("Round-trip: insert → toRawString → re-parse should preserve the parameter", do
      let raw := (URI.Query.empty.insert "a&b" "c=d").toRawString
      expectEq "get" ((← queryOf s!"/path?{raw}").get "a&b") (some "c=d")),
    ("sampleQuery", do
      let q ← queryOf s!"/path?{sampleQuery.toRawString}"
      ensure (q == sampleQuery && q.get "a+b" == some "x+y") "reparsed sampleQuery"),
    ("A name containing `=` is percent-encoded, so it still reads back as the name", do
      let uri := URI.Builder.empty
        |>.setScheme! "http" |>.setHost! "example.com" |>.addQueryParam "k=1" "v=2" |>.build
      expectEq "get" (((URI.parse? (toString uri)).bind (·.query)).bind (·.get "k=1")) (some "v=2"))
  ] (·.2)

#eval checkCases "Query Operations" #[
    ("insert then contains", ensure (URI.Query.empty.insert "a" "1" |>.contains "a") "contains a"),
    ("empty contains nothing", ensure (!URI.Query.empty.contains "nonexistent") "contains nonexistent"),
    ("insert a, b", expectEq "toRawString" (URI.Query.empty |>.insert "a" "1" |>.insert "b" "2").toRawString
      "a=1&b=2"),
    ("erase a", expectEq "toRawString"
      (URI.Query.empty |>.insert "a" "1" |>.insert "b" "2" |>.erase "a").toRawString "b=2"),
    ("set replaces", expectEq "toRawString"
      (URI.Query.empty |>.insert "key" "old" |>.set "key" "new").toRawString "key=new")
  ] (·.2)

-- A name's `=` is printed escaped, or it would end the name when the query is read back. A value
-- keeps its `=` as is.
#eval checkCases "Query names containing `=` (#16021)" #[
    ("a=b with value c=d", ensure (match URI.EncodedQueryParam.fromString? "a=b", URI.EncodedQueryParam.fromString? "c=d" with
      | some key, some value =>
        let printed := toString (URI.Query.empty.insertEncoded key (some value))
        printed == "?a%3Db=c=d" &&
          (RequestTarget.parse? ("/p" ++ printed)).map (·.query.get "a=b") == some (some "c=d")
      | _, _ => false) "?a%3Db=c=d"),
    ("= as a flag", ensure (match URI.EncodedQueryParam.ofByteArray? "=".toUTF8 with
      | some key =>
        let printed := toString (URI.Query.empty.insertEncoded key none)
        printed == "?%3D" && (RequestTarget.parse? ("/p" ++ printed)).map (·.query.contains "=") == some true
      | none => false) "?%3D")
  ] (·.2)

#eval checkCases "Updates keep the other spellings of a name (#15246)" #[
    ("toRawString re-escapes a literal %", expectEq "toRawString" sampleQuery.toRawString
      "a%2Bb=x%2By&a+b=x+y&a%252Bb=%252B"),
    ("erase", do
      let erased := sampleQuery.erase "a+b"
      ensure (!erased.contains "a+b" && erased.get "a b" == some "x y" && erased.get "a%2Bb" == some "%2B")
        "erase a+b"),
    ("set", do
      let updated := sampleQuery.set "a+b" "+"
      ensure (updated.get "a+b" == some "+" && updated.get "a b" == some "x y" &&
        updated.get "a%2Bb" == some "%2B" && (updated.findAll "a+b").size == 1) "set a+b")
  ] (·.2)

/-! ## Query syntax (RFC 3986 §3.4) -/

#eval checkCases "Query syntax" #[
    ("A trailing `&` is accepted and produces an empty-key entry", do
      expectEq "size" (← queryOf "/path?key=val&").size 2),
    ("A value may contain an unencoded `=`: the name ends at the first `=` (#16021)", do
      expectEq "find?" (reprLine ((← queryOf "/path?key=a=b").find? "key")) "some (some \"a=b\")"),
    ("A percent-encoded `=` in the value is preserved as-is", do
      expectEq "find?" (reprLine ((← queryOf "/path?key=a%3Db").find? "key")) "some (some \"a%3Db\")"),
    ("`none` means no query delimiter", ensure (URI.parse! "http://example.com/path").query.isNone
      "query of http://example.com/path"),
    ("`some .empty` means an explicit empty query", ensure (match (URI.parse! "http://example.com/path?").query with
      | some q => q.isEmpty && toString (URI.parse! "http://example.com/path?") == "http://example.com/path?"
      | none => false) "http://example.com/path?"),
    ("RequestTarget /path?", ensure (match RequestTarget.parse? "/path?" with
      | some (.originForm _ (some q)) => q.isEmpty && toString (RequestTarget.parse! "/path?") == "/path?"
      | _ => false) "/path?"),
    ("URIReference ?", ensure (match URIReference.parse? "?" with
      | some (.relative ref) => ref.query.isSome && toString (URIReference.parse! "?") == "?"
      | _ => false) "?"),
    ("URIReference #frag", ensure (match URIReference.parse? "#frag" with
      | some (.relative ref) => ref.query.isNone && toString (URIReference.parse! "#frag") == "#frag"
      | _ => false) "#frag")
  ] (·.2)


#eval checkCases "Names and values of a query (RFC 3986 §3.4)" #[
    ("=: an empty name and an empty value", "=", #[("", some "")]),
    ("=a: an empty name", "=a", #[("", some "a")]),
    ("a: a name with no value", "a", #[("a", none)]),
    ("a=: an empty value", "a=", #[("a", some "")]),
    ("a=1&a=2: repeated names are kept, in order", "a=1&a=2", #[("a", some "1"), ("a", some "2")]),
    (";a=b: `;` is not a separator", ";a=b", #[(";a", some "b")]),
    ("a=1;b=2: one parameter", "a=1;b=2", #[("a", some "1;b=2")]),
    ("a=a+b;b=b+c: `+` decodes to a space", "a=a+b;b=b+c", #[("a", some "a b;b=b c")])
  ] fun (label, q, want) => do
    let query ← queryOf s!"/p?{q}"
    let got := Array.map (fun (k, v) => (k.decode.getD (toString k), v.map fun v => v.decode.getD (toString v))) query
    expectEq label got want

#eval checkCases "`?`, `/` and `:` stay in the query (RFC 3986 §3.4)" #[
    ("?foo=bar?", expectEq "foo" ((URI.parse! "http://example.com/p?foo=bar?").query.bind (·.get "foo")) (some "bar?")),
    ("?query=http://bad", do
      let some t := RequestTarget.parse? "/p?query=http://bad" | throw <| IO.userError "did not parse"
      ensure (t matches .originForm _ _) "not origin-form"
      expectEq "query" (t.query.get "query") (some "http://bad"))
  ] (·.2)

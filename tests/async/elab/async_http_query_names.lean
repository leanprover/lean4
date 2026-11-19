import Std.Http

open Std Http

/-!
Tests `URI.Query.names`: the unique parameter names in order of first occurrence, at a cost linear in
the number of parameters, since a request-target may carry up to `maxUriLength` of them. Also tests
that `String`-keyed lookups match a name exactly when it decodes to the key.
-/

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

#eval show IO Unit from do
  let names := (RequestTarget.parse! "/?b=1&a&b=2&c=&a=3&%61").query.names.map toString
  expect (names == #["b", "a", "c", "%61"]) s!"names {names}"

-- A quadratic deduplication takes seconds here; a linear one, milliseconds.
#eval show IO Unit from do
  let n := 40000
  let query := (List.range n).foldl (fun q i => q.insert s!"k{i}" "v") URI.Query.empty
  let start ← IO.monoMsNow
  let names ← IO.lazyPure fun _ => query.names
  -- Checked before the clock is read again, so the names are computed in between.
  expect (names.size == n) s!"{names.size} names"
  let elapsed := (← IO.monoMsNow) - start
  expect (elapsed < 2000) s!"Query.names took {elapsed} ms for {n} distinct names"

-- `String`-keyed lookups compare a name as it decodes, byte by byte without decoding it into a new
-- string; this must agree with decoding and comparing.
#eval show IO Unit from do
  let cases : List (String × String) := [
    ("a%3Ab", "a:b"), ("a%3ab", "a:b"), ("a+b", "a b"), ("a%2Bb", "a+b"), ("a+b", "a+b"),
    ("abc", "abc"), ("abc", "ab"), ("ab", "abc"), ("%41", "A"), ("%41", "a"),
    ("r%C3%A9sum%C3%A9", "résumé"), ("%E9", "é"), ("%C3", "Ã"), ("", ""), ("x", "")]
  for (enc, key) in cases do
    let some name := URI.EncodedQueryParam.ofByteArray? enc.toUTF8
      | throw (IO.userError s!"{enc} is not a valid query name")
    let query := (RequestTarget.parse! s!"/?{enc}=v").query
    let expected := name.decode == some key
    expect (query.contains key == expected) s!"contains {key.quote} on {enc}: expected {expected}"
    expect ((query.get key).isSome == expected) s!"get {key.quote} on {enc}: expected {expected}"

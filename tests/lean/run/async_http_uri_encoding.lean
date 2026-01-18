import Std.Internal.Http.Data.URI.Encoding

open Std.Http.URI

-- Valid percent encoding tests

/--
info: some "abc"
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "abc".toUTF8))

/--
info: some "%20"
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%20".toUTF8))

/--
info: some "hello%20world"
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "hello%20world".toUTF8))

/--
info: some "%20%21"
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%20%21".toUTF8))

/--
info: some "%FF"
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%FF".toUTF8))

/--
info: some "%00"
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%00".toUTF8))

-- Invalid percent encoding tests: % alone
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "hello%".toUTF8))

-- Invalid percent encoding tests: % followed by only one hex digit
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%2".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "hello%2".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%A".toUTF8))

-- Invalid percent encoding tests: % followed by non-hex characters
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%GG".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%2G".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedString.ofByteArray? "%G2".toUTF8))

/--
info: some "hello+world"
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? "hello+world".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? "%".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? "%2".toUTF8))

/--
info: some "%20"
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? "%20".toUTF8))


-- Valid percent encoding tests

/--
info: some "abc"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "abc".toUTF8))

/--
info: some " "
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%20".toUTF8))

/--
info: some "hello world"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "hello%20world".toUTF8))

/--
info: some " !"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%20%21".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%FF".toUTF8))

/--
info: some "\x00"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%00".toUTF8))

-- Invalid percent encoding tests: % alone
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "hello%".toUTF8))

-- Invalid percent encoding tests: % followed by only one hex digit
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%2".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "hello%2".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%A".toUTF8))

-- Invalid percent encoding tests: % followed by non-hex characters
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%GG".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%2G".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedString.decode =<< (EncodedString.ofByteArray? "%G2".toUTF8))

/--
info: some "hello world"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode =<< (EncodedQueryString.ofByteArray? "hello+world".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode =<< (EncodedQueryString.ofByteArray? "%".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode =<< (EncodedQueryString.ofByteArray? "%2".toUTF8))

/--
info: some " "
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode =<< (EncodedQueryString.ofByteArray? "%20".toUTF8))

import Std.Http.Internal.String
import Std.Http.Internal.Char

open Std.Http.Internal

private def c (n : Nat) : Char := Char.ofNat n

#guard Std.Http.Internal.Char.qdtext (c 0x08) = false
#guard Std.Http.Internal.Char.qdtext (c 0x09) = true
#guard Std.Http.Internal.Char.qdtext (c 0x0a) = false
#guard Std.Http.Internal.Char.qdtext (c 0x1f) = false
#guard Std.Http.Internal.Char.qdtext (c 0x20) = true
#guard Std.Http.Internal.Char.qdtext (c 0x21) = true
#guard Std.Http.Internal.Char.qdtext (c 0x22) = false
#guard Std.Http.Internal.Char.qdtext (c 0x23) = true
#guard Std.Http.Internal.Char.qdtext (c 0x5b) = true
#guard Std.Http.Internal.Char.qdtext (c 0x5c) = false
#guard Std.Http.Internal.Char.qdtext (c 0x5d) = true
#guard Std.Http.Internal.Char.qdtext (c 0x7e) = true
#guard Std.Http.Internal.Char.qdtext (c 0x7f) = false

#guard Std.Http.Internal.Char.quotedPairChar (c 0x08) = false
#guard Std.Http.Internal.Char.quotedPairChar (c 0x09) = true
#guard Std.Http.Internal.Char.quotedPairChar (c 0x1f) = false
#guard Std.Http.Internal.Char.quotedPairChar (c 0x20) = true
#guard Std.Http.Internal.Char.quotedPairChar (c 0x21) = true
#guard Std.Http.Internal.Char.quotedPairChar (c 0x22) = true
#guard Std.Http.Internal.Char.quotedPairChar (c 0x5c) = true
#guard Std.Http.Internal.Char.quotedPairChar (c 0x7e) = true
#guard Std.Http.Internal.Char.quotedPairChar (c 0x7f) = false

#guard Std.Http.Internal.Char.quotedStringChar (c 0x09) = true
#guard Std.Http.Internal.Char.quotedStringChar (c 0x20) = true
#guard Std.Http.Internal.Char.quotedStringChar (c 0x22) = true
#guard Std.Http.Internal.Char.quotedStringChar (c 0x5c) = true
#guard Std.Http.Internal.Char.quotedStringChar (c 0x0a) = false
#guard Std.Http.Internal.Char.quotedStringChar (c 0x0d) = false
#guard Std.Http.Internal.Char.quotedStringChar (c 0x7f) = false

#guard quoteHttpString? "token" = some "token"
#guard quoteHttpString? "a\t " = some "\"a\t \""
#guard quoteHttpString? "atabpo\n\t " = none
#guard quoteHttpString? "" = some "\"\""
#guard quoteHttpString? "\"" = some "\"\\\"\""
#guard quoteHttpString? "\\" = some "\"\\\\\""
#guard quoteHttpString? "\"\\\"" = some "\"\\\"\\\\\\\"\""
#guard quoteHttpString? "abc\rdef" = none
#guard quoteHttpString? "abc\ndef" = none
#guard quoteHttpString? "abc\u0000def" = none

#guard unquoteHttpString? "\"token\"" = some "token"
#guard unquoteHttpString? "\"a\\\\\\\"b\"" = some "a\\\"b"
#guard unquoteHttpString? "\"line1\nline2\"" = none
#guard unquoteHttpString? "\"\"" = some ""
#guard unquoteHttpString? "\"\\\\\"" = some "\\"
#guard unquoteHttpString? "\"\\\"\"" = some "\""
#guard unquoteHttpString? "\"a\\tb\"" = some "atb"
#guard unquoteHttpString? "\"a\tb\"" = some "a\tb"
#guard unquoteHttpString? "token" = some "token"
#guard unquoteHttpString? "\"" = none
#guard unquoteHttpString? "\"abc" = none
#guard unquoteHttpString? "\"abc\\\"" = none
#guard unquoteHttpString? "\"abc\\\n\"" = none
#guard unquoteHttpString? "\"abc\r\"" = none

private def isQuotedString (s : String) : Bool :=
  s.startsWith '"' && (unquoteHttpString? s).isSome

#guard isQuotedString "\"abc\"" = true
#guard isQuotedString "\"ab\\\\\\\"c\"" = true
#guard isQuotedString "\"ab\nc\"" = false
#guard isQuotedString "\"\"" = true
#guard isQuotedString "\"\\\"\"" = true
#guard isQuotedString "\"\\\\\"" = true
#guard isQuotedString "abc" = false
#guard isQuotedString "\"" = false
#guard isQuotedString "\"abc" = false
#guard isQuotedString "\"abc\\\"" = false

#guard unquoteHttpString? (quoteHttpString! "abc\t ") = some "abc\t "
#guard unquoteHttpString? (quoteHttpString! "a\\\"b") = some "a\\\"b"
#guard unquoteHttpString? (quoteHttpString! "") = some ""
#guard unquoteHttpString? (quoteHttpString! "\"") = some "\""
#guard unquoteHttpString? (quoteHttpString! "\\") = some "\\"
#guard unquoteHttpString? (quoteHttpString! " !#$%&'()*+,-./:;<=>?@[\\]^_`{|}~") = some " !#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"

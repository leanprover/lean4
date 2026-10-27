import Lean.Data.Json
open Lean

/-!
Regression test for #16018: strings with non-ASCII characters went through the per-character
escaping path, and now take the fast path.  This checks that their output is unchanged, with and
without characters that need escaping; it does not measure which path is taken.
-/

#guard (Json.str "héllo wörld").compress == "\"héllo wörld\""
#guard (Json.str "日本語 😀").compress == "\"日本語 😀\""
#guard (Json.str "é\"ü\\ö\nä").compress == "\"é\\\"ü\\\\ö\\nä\""
#guard (Json.str "é\x01").compress == "\"é\\u0001\""
#guard (Json.str "a\x7fb\u0085c").compress == "\"a\x7fb\u0085c\""
#guard (Json.mkObj [("clé", Json.str "valeur à vérifier")]).compress == "{\"clé\":\"valeur à vérifier\"}"
#guard (Json.arr #[Json.str "naïve", Json.str "ça"]).pretty == "[\"naïve\", \"ça\"]"
#guard Json.escape "naïve" "x" == "xnaïve"

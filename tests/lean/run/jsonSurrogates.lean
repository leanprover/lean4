import Lean.Data.Json

#guard (Lean.Json.parse "\"\\ud835\\udd5c\"").toOption.get! == Lean.Json.str "𝕜"
#guard (Lean.Json.parse "\"\\ud835\"").toOption.get! == Lean.Json.str "\ufffd"
#guard (Lean.Json.parse "\"\\udd5c\"").toOption.get! == Lean.Json.str "\ufffd"
#guard (Lean.Json.parse "\"\\ud823\\ud835\\udd5c\"").toOption.get! == Lean.Json.str "\ufffd𝕜"

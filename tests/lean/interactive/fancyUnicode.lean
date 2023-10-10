-- encoding: [[], ["utf-8"], ["utf-16"], ["utf-32"], ["utf-32", "utf-16"]]

/-! Test Unicode handling in the server by using identifiers and
strings that are multi-byte in variable-width encodings. -/

def 𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟 := 23

            --v textDocument/completion
example := 𝓟𝓟𝓟𝓟
          --^ textDocument/completion


example := 𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟
           --^ textDocument/documentHighlight
   --^ textDocument/documentHighlight
                  --^ textDocument/documentHighlight
                   --^ textDocument/documentHighlight

theorem arr : ∃s, s = "🇩🇰" := by constructor; trivial
                              --^ goals
                                 --^ goals
                                  --^ goals
                                            --^ goals
                                              --^ goals
                                               --^ goals
                                                     --^ goals
def «🍋» := "lemon"
 --^ textDocument/documentHighlight
  --^ textDocument/documentHighlight
    --^ textDocument/documentHighlight
     --^ textDocument/documentHighlight


theorem lemon_is_lemon : «🍋» = "le" ++ "mon" := by rfl
                                                 --^ goals
                                                  --^ goals

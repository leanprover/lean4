-- encoding: [[], ["utf-8"], ["utf-16"], ["utf-32"], ["utf-32", "utf-16"]]
def 𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟 := 23

            --v textDocument/completion
example := 𝓟𝓟𝓟𝓟
          --^ textDocument/completion


example := 𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟𝓟
           --^ textDocument/documentHighlight
   --^ textDocument/documentHighlight
                  --^ textDocument/documentHighlight
                   --^ textDocument/documentHighlight

def A.B1.verySpecificDefinitionNameOfCompletionOpenNamespaces := 1
open A B1

namespace A
def c2 : Nat := verySpecificDefinitionNameOfCompletionOpenNamespaces
                                                                  --^ textDocument/completion

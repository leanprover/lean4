def A.B1.verySpecificDefinitionNameOfCompletionOpenNamespaces := 1

namespace A.B2

private def verySpecificDefinitionNameOfCompletionOpenNamespacesPrivate := 2

end A.B2

open A B1

namespace A
def c2 : Nat := verySpecificDefinitionNameOfCompletionOpenNamespaces
                                                                  --^ completion

def c3 : Nat := verySpecificDefinitionNameOfCompletionOpenNamespacesPriv
                                                                     --^ completion

def c4 : Nat := B2.verySpecificDefinitionNameOfCompletionOpenNamespacesPriv
                                                                        --^ completion

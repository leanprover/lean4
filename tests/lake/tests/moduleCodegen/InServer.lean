module

import Test.A

/-!
Built with `Elab.inServer`, this module is elaborated at the `.server` level, where `#eval` may run
a plainly imported definition. The build must then provide the import's IR although this module
postpones its own code generation.
-/

#eval twice 21

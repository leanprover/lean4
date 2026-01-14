module

prelude
import all Module.ImportedAll

/-! `import all` should chain with nested `import all`s. -/

#check priv

#check { x := 1 : StructWithPrivateField }

#check (⟨1⟩ : StructWithPrivateField)

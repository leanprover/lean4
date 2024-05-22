Functions defined by well-founded recursion are now marked as
`@[irreducible]`, which should prevent expensive and often unfruitful
unfolding of such definitions.

Existing proofs that hold by definitional equality (e.g. `rfl`) can be
rewritten to explictly unfold the function definition (using `simp`,
`unfold`, `rw`), or the recursive function can be temporariliy made
semireducible (using `unseal f in` before the command) or the function
definition itself can be marked as `@[semireducible]` to get the previous
behavor.

#4061

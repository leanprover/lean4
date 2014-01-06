Builtin libraries and scripts
------------------------------

This directory contains builtin Lean theories and additional Lua
scripts that are distributed with Lean. Some of the theories (e.g.,
`kernel.lean`) are automatically loaded when we start Lean. Others
must be imported using the `import` command.

Several Lean components rely on these libraries. For example, they use
the axioms and theorems defined in these libraries to build proofs.



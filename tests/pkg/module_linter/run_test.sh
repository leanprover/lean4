rm -rf .lake

# Build the library; the module linter registered in `ModLinter.Def` runs over the
# whole `ModLinter` module and emits a warning at its terminal command.
capture lake build

# The linter prints the whole module's command syntax. The pretty printer wraps the
# array across lines, so match a stable single-line prefix proving it saw all commands.
check_out_contains "cmds: [def a :="

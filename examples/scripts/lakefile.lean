import Lake
open Lake DSL

package scripts

/--
Display a greeting

USAGE:
  lake run greet [name]

Greet the entity with the given name. Otherwise, greet the whole world.
-/
@[default_script]
script greet (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args[0]'h}!"
  else
    IO.println "Hello, world!"
  return 0


@[default_script]
script dismiss do
  IO.println "Goodbye!"
  return 0

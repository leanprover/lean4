import Lake
open Lake DSL

package scripts

script greet (args) do
  if h : 0 < args.length then
    IO.println s!"Hello, {args.get 0 h}!"
  else
    IO.println "Hello, world!"
  pure 0

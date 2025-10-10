import Lake
open Lake DSL

package dep

@[default_script]
script hello do
  IO.println "Hello from Dep!"
  return 0

import Lean

def explode (x : Nat) : IO Unit := do
  if x == 0  then IO.println "arg is 0"
  if x == 1  then IO.println "arg is 1"
  if x == 2  then IO.println "arg is 2"
  if x == 3  then IO.println "arg is 3"
  if x == 4  then IO.println "arg is 4"
  if x == 5  then IO.println "arg is 5"
  if x == 6  then IO.println "arg is 6"
  if x == 7  then IO.println "arg is 7"
  if x == 8  then IO.println "arg is 8"
  if x == 9  then IO.println "arg is 9"
  if x == 10 then IO.println "arg is 10"
  if x == 11 then IO.println "arg is 11"
  if x == 12 then IO.println "arg is 12"
  if x == 13 then IO.println "arg is 13"
  if x == 14 then IO.println "arg is 14"
  if x == 15 then IO.println "arg is 15"
  if x == 16 then IO.println "arg is 16"
  if x == 17 then IO.println "arg is 17"
  if x == 18 then IO.println "arg is 18"
  if x == 19 then IO.println "arg is 19"
  if x == 20 then IO.println "arg is 20"

#eval Lean.Compiler.compile #[``explode]

set_option trace.Compiler.result true
#eval Lean.Compiler.compile #[``explode]

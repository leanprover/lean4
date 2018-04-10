import system.io
open io

def main : io unit :=
do { l ← get_line,
     if l = "hello" then
       put_str "you have typed hello\n"
     else
       do {put_str "you did not type hello\n", put_str "-----------\n"} }

#lang lean4
def main (xs : List String) : IO UInt32 :=
IO.println "hello world" *>
pure 0

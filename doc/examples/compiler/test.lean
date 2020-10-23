#lang lean4
def main (n : List String) : IO UInt32 := do
   IO.println (toString n)
   pure 0

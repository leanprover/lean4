def main (args : List String) : IO UInt32 :=
  pure <| UInt32.ofNat args.length

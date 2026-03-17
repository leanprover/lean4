def main (args : List String) : IO UInt32 := do
  for (arg : String) in args do
    match arg with
    | "--print-cflags" =>
      return 1
    | _ =>
      pure ()
  return 0

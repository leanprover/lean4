/-! A program for the `sandbox` test to run: it prints a variable the sandbox withholds. -/

def main (args : List String) : IO UInt32 := do
  IO.println s!"secret={(← IO.getEnv "SANDBOX_TEST_SECRET").getD ""}"
  return if args.isEmpty then 0 else 4

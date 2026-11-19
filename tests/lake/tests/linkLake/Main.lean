import Lake.All

/-!
Root of an executable that links against Lake, to check that the toolchain's static link line
covers every library Lake references.
-/

def main : IO Unit :=
  IO.println s!"Lake {Lake.versionStringCore}"

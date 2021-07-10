import Lake.Package

def package : Lake.Packager := fun path args => do
  IO.println s!"computing io package in {path} with args {args} ..."
  return {
    name := "io"
    version := "1.0"
  }

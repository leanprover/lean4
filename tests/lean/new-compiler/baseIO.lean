set_option trace.compiler.saveBase true
def test : BaseIO UInt32 := do
  let ref ← IO.mkRef 42
  ref.set 10
  ref.get

/-!
Tests the out-of-bounds behavior of `get!` and `set!` on `ByteArray` and `FloatArray`, both for
indices that fit into a scalar `Nat` and for indices that do not.
-/

@[noinline] def big (n : Nat) : Nat := 2 ^ (64 + n)

def main (args : List String) : IO Unit := do
  let n := args.length
  let bs : ByteArray := ⟨#[1, 2, 3]⟩
  IO.eprintln "ByteArray.get! in bounds"
  IO.eprintln (bs.get! (n + 1))
  IO.eprintln "ByteArray.get! small out of bounds"
  IO.eprintln (bs.get! (n + 3))
  IO.eprintln "ByteArray.get! big out of bounds"
  IO.eprintln (bs.get! (big n))
  IO.eprintln "ByteArray.set! in bounds"
  IO.eprintln (bs.set! (n + 1) 7).data
  IO.eprintln "ByteArray.set! small out of bounds"
  IO.eprintln (bs.set! (n + 3) 7).data
  IO.eprintln "ByteArray.set! big out of bounds"
  IO.eprintln (bs.set! (big n) 7).data

  let fs : FloatArray := ⟨#[1, 2, 3]⟩
  IO.eprintln "FloatArray.get! in bounds"
  IO.eprintln (fs.get! (n + 1))
  IO.eprintln "FloatArray.get! small out of bounds"
  IO.eprintln (fs.get! (n + 3))
  IO.eprintln "FloatArray.get! big out of bounds"
  IO.eprintln (fs.get! (big n))
  IO.eprintln "FloatArray.set! in bounds"
  IO.eprintln (fs.set! (n + 1) 7).data
  IO.eprintln "FloatArray.set! small out of bounds"
  IO.eprintln (fs.set! (n + 3) 7).data
  IO.eprintln "FloatArray.set! big out of bounds"
  IO.eprintln (fs.set! (big n) 7).data

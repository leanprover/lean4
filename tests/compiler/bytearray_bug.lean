def main (xs : List String) : IO Unit :=
  let arr := (let e := ByteArray.empty in e.push (UInt8.ofNat 10)) in
  let v := arr.data.get 0 in
  IO.println v

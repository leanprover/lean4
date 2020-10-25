
def main (xs : List String) : IO Unit :=
  let arr := (let e := ByteArray.empty; e.push (UInt8.ofNat 10));
  let v := arr.data.get! 0;
  IO.println v

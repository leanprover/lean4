example (x : Nat) (_h :
    let v := Vector.ofFn fun k : Fin 5 => (x >>> k.val) % 2 != 0
    (Vector.ofFn fun i : Fin 1 =>
      Fin.foldl 5 (fun (acc : BitVec 1) j => acc + v[i.val + j.val].toNat) 0)[0] = 0) : True := by
  simp only [Vector.getElem_ofFn] at _h
  trivial

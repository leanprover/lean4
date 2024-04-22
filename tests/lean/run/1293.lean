theorem modifySize {A : Type u} (as : Array A) (f : A → A) (n : Nat) : (as.modify n f).size = as.size := by
  simp [Array.modify, Array.modifyM, Id.run]; split <;> simp [Id.run]

structure Idx (p : Array String) where
  n : Fin p.size

structure Store where
  arr : Array String
  -- integer pointers into `arr`, type-indexed by `arr`
  ids : Array (Idx arr)

instance {arr : Array String} {f : String → String} {n : Nat} : Coe (Array (Idx arr)) (Array (Idx (arr.modify n f))) where
  coe xs :=
    xs.map (fun x => Idx.mk ((modifySize arr f n) ▸ x.n))

def store1 : Store := {
  arr := #["a", "b", "c", "d", "e"]
  ids := #[⟨2, by decide⟩]
}

def tryCoeStore := {
  store1 with
  -- using a lambda here hangs
  arr := store1.arr.modify 2 (fun _ => "Z")
}

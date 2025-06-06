prelude
import Std.Data.Ranges.Slice

instance : Sliceable shape (Array α) Nat α where

instance : SliceIter ⟨.none, .none⟩ (Array α) Nat :=
  .of (·.collection.iter)

instance : SliceIter ⟨.closed, .none⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.drop s.range.lower)

instance : SliceIter ⟨.open, .none⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.drop (s.range.lower + 1))

instance : SliceIter ⟨.none, .closed⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1))

instance : SliceIter ⟨.closed, .closed⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1) |>.drop s.range.lower)

instance : SliceIter ⟨.open, .closed⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take (s.range.upper + 1) |>.drop (s.range.lower + 1))

instance : SliceIter ⟨.none, .open⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper)

instance : SliceIter ⟨.closed, .open⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper |>.drop s.range.lower)

instance : SliceIter ⟨.open, .open⟩ (Array α) Nat :=
  .of (fun s => s.collection.iter.take s.range.upper |>.drop (s.range.lower + 1))

def testArray : Array Nat := #[0, 1, 2, 3, 4, 5, 6]

#eval testArray[[2<,,]].iter.toList

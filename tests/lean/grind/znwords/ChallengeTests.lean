
import Init.Grind
import Init.Data.BitVec
import Init.Data.Fin.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.UInt
import Init.Data.SInt.Basic




-- Shim for prototype names
abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat
abbrev BitVec.signed {w} (x : BitVec w) := x.toInt

-- Missing instances in standard Lean
def Fin.lnot {n : Nat} (a : Fin n) : Fin n := ⟨n - 1 - a.val, by have := a.isLt; omega⟩
instance {n : Nat} : Complement (Fin n) where complement := Fin.lnot

@[grind hom] theorem Fin.val_lnot {n : Nat} (a : Fin n) : (~~~a).val = n - 1 - a.val := rfl

-- Compatibility lemmas for ported tests
theorem BitVec.toNat_eq_unsigned {w} (x : BitVec w) : x.toNat = x.unsigned := rfl


example (α : Type) (l1 l2 : List α) (x : α) (a b : Int)
  (h_len : (l1 ++ l2).length = (a + b).toNat)
  (_h_a : a < b) :
  (((l1.take a.toNat).reverse ++ (l2.drop b.toNat)).concat x).length ≤ (a + b).toNat + 1 := by grind

example (α : Type) (l1 l2 : List α) (x : α) (a b : BitVec 32)
  (h_len : (l1 ++ l2).length = (a + b).toNat)
  (_h_a : a < b) :
  (((l1.take a.toNat).reverse ++ (l2.drop b.toNat)).concat x).length ≤ (a + b).toNat + 1 := by grind

example (α : Type) (l1 l2 : List α) (x : α) (a b : BitVec 32)
  (h_len : (l1 ++ l2).length = (a + b).toNat)
  (_h_a : a < b) :
  (((l1.take a.toNat).reverse ++ (l2.drop b.toNat)).concat x).length ≤ (a + b).unsigned + 1 := by grind

example (α : Type) (default_val : α) (a b : Int) :
  let sz := if a ≤ b then a.toNat else b.toNat;
  let l := List.replicate sz default_val;
  let l' := l.modify (sz / 2) id;
  l'.length ≤ a.toNat ∧ l'.length ≤ b.toNat := by grind

example (α : Type) (default_val : α) (a b : BitVec 32) :
  let sz := if a ≤ b then a.toNat else b.toNat;
  let l := List.replicate sz default_val;
  let l' := l.modify (sz / 2) id;
  l'.length ≤ a.toNat ∧ l'.length ≤ b.toNat := by grind

example (α : Type) (default_val : α) (a b : BitVec 32) :
  let sz := if a ≤ b then a.unsigned else b.unsigned;
  let l := List.replicate sz.toNat default_val;
  let l' := l.modify (sz.toNat / 2) id;
  l'.length ≤ a.toNat ∧ l'.length ≤ b.toNat := by grind

example (α : Type) [BEq α] (default_val : α) (l1 l2 : List α) (i : Nat) :
  let z := List.zipWith (fun x _ => x) l1 l2;
  let s := z.set i default_val;
  let m := s.insertIdx i default_val;
  let e := m.eraseIdx i;
  let r := e.replace default_val default_val;
  let f := r.dropLast;
  f.length ≤ l1.length ∧ f.length ≤ l2.length := by grind

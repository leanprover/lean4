def S := List Nat
opaque TSpec : NonemptyType
def T (s : S) : Type :=  TSpec.type
instance (s : S) : Nonempty (T s) :=
  TSpec.property

inductive Op : (ishapes : List S) → (oshape : S) → Type
  | binary : (shape : S) → Op [shape, shape] shape
  | gemm   : {m n p : Nat} → Op [[m, n], [n, p]] [m, p]

noncomputable def Op.f : {ishapes : List S} → {oshape : S} → Op ishapes oshape → T oshape
  | [shape, _],        _,      binary _ => Classical.ofNonempty
  | [[m, n], [_, p]],  [_, _], gemm     => Classical.ofNonempty

#print Op.f

noncomputable def Op.f2 : {ishapes : List S} → {oshape : S} → Op ishapes oshape → T oshape
  | _,  _, binary _ => Classical.ofNonempty
  | _,  _, gemm     => Classical.ofNonempty

#print Op.f2

noncomputable def Op.f2' {ishapes : List S} {oshape : S} : Op ishapes oshape → T oshape
  | binary _ => Classical.ofNonempty
  | gemm     => Classical.ofNonempty

noncomputable def Op.f2'' : Op i o → T o
  | binary _ => Classical.ofNonempty
  | gemm     => Classical.ofNonempty

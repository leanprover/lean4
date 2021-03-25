def S := List Nat
constant TSpec : PointedType
def T (s : S) : Type :=  TSpec.type
instance (s : S) : Inhabited (T s) := {
  default := TSpec.val
}

inductive Op : (ishapes : List S) → (oshape : S) → Type
  | binary : (shape : S) → Op [shape, shape] shape
  | gemm   : {m n p : Nat} → Op [[m, n], [n, p]] [m, p]

def Op.f : {ishapes : List S} → {oshape : S} → Op ishapes oshape → T oshape
  | [shape, _],        _,      binary _ => arbitrary
  | [[m, n], [_, p]],  [_, _], gemm     => arbitrary

#print Op.f

def Op.f2 : {ishapes : List S} → {oshape : S} → Op ishapes oshape → T oshape
  | _,  _, binary _ => arbitrary
  | _,  _, gemm     => arbitrary

#print Op.f2

def Op.f2' {ishapes : List S} {oshape : S} : Op ishapes oshape → T oshape
  | binary _ => arbitrary
  | gemm     => arbitrary

def Op.f2'' : Op i o → T o
  | binary _ => arbitrary
  | gemm     => arbitrary

inductive Ty :=
| int: Ty
| other: Ty

inductive Tensor :=
| int: Int -> Tensor
| nested: List Tensor -> Tensor

def hasBaseType: Tensor → Ty → Bool
  | .int _, Ty.int      => true
  | .int _, Ty.other    => true
  | .nested _, _        => true

def flatten (e: Tensor) (τ: Ty) (h: hasBaseType e τ): List Int :=
  match e, τ with
  | .int _, Ty.int     => []
  | .int _, _          => []
  | .nested [], _      => []
  | .nested (_::_), _  => []

theorem flatten_list (l: List Tensor) τ (h: hasBaseType (.nested l) τ):
    flatten (.nested l) τ h = [] := by
  simp [flatten]
  repeat sorry

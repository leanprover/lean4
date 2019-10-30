import Init.Lean.Level

namespace Lean
namespace Level

def mkMax (xs : Array Level) : Level :=
xs.foldlFrom max (xs.get! 0) 1

#eval toString $ normalize $ succ $ succ $ mkMax #[zero, param `w, succ (succ (succ (param `z))), one, succ (succ (param `x)), zero, param `x, param `y, param `x, param `z, succ one, param `w, succ (param `x)]
#eval toString $ normalize $ max zero (param `x)
#eval toString $ normalize $ max (param `x) zero
#eval toString $ normalize $ max zero one
#eval toString $ normalize $ succ (max (param `x) (param `x))
#eval toString $ normalize $ max (imax (param `x) one) (max (succ (param `x)) (param `x))
#eval toString $ normalize $ imax (imax (param `x) one) (max (succ (param `x)) (param `x))
#eval toString $ #[zero, succ (succ (param `z)), one, succ (succ (param `x)), zero, param `x, param `y, param `x, param `z, succ (param `x)].qsort normLt

end Level
end Lean

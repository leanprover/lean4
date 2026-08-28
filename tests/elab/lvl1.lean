import Lean.Level

namespace Lean
namespace Level

def mkMax (xs : Array Level) : Level :=
xs.foldl (start := 1) (init := xs[0]!) mkLevelMax

#eval toString $ normalize $ mkLevelSucc $ mkLevelSucc $ mkMax #[Level.zero, mkLevelParam `w, mkLevelSucc (mkLevelSucc (mkLevelSucc (mkLevelParam `z))), Level.one, mkLevelSucc (mkLevelSucc (mkLevelParam `x)), Level.zero, mkLevelParam `x, mkLevelParam `y, mkLevelParam `x, mkLevelParam `z, mkLevelSucc Level.one, mkLevelParam `w, mkLevelSucc (mkLevelParam `x)]
#eval toString $ normalize $ mkLevelMax Level.zero (mkLevelParam `x)
#eval toString $ normalize $ mkLevelMax (mkLevelParam `x) Level.zero
#eval toString $ normalize $ mkLevelMax Level.zero Level.one
#eval toString $ normalize $ mkLevelSucc (mkLevelMax (mkLevelParam `x) (mkLevelParam `x))
#eval toString $ normalize $ mkLevelMax (mkLevelIMax (mkLevelParam `x) Level.one) (mkLevelMax (mkLevelSucc (mkLevelParam `x)) (mkLevelParam `x))
#eval toString $ normalize $ mkLevelIMax (mkLevelIMax (mkLevelParam `x) Level.one) (mkLevelMax (mkLevelSucc (mkLevelParam `x)) (mkLevelParam `x))
#eval toString $ #[Level.zero, mkLevelSucc (mkLevelSucc (mkLevelParam `z)), Level.one, mkLevelSucc (mkLevelSucc (mkLevelParam `x)), Level.zero, mkLevelParam `x, mkLevelParam `y, mkLevelParam `x, mkLevelParam `z, mkLevelSucc (mkLevelParam `x)].qsort normLt

end Level
end Lean

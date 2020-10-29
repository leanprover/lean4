import Lean.Level

namespace Lean
namespace Level

def mkMax (xs : Array Level) : Level :=
xs.foldl (start := 1) (init := xs[0]) mkLevelMax

#eval toString $ normalize $ mkLevelSucc $ mkLevelSucc $ mkMax #[levelZero, mkLevelParam `w, mkLevelSucc (mkLevelSucc (mkLevelSucc (mkLevelParam `z))), levelOne, mkLevelSucc (mkLevelSucc (mkLevelParam `x)), levelZero, mkLevelParam `x, mkLevelParam `y, mkLevelParam `x, mkLevelParam `z, mkLevelSucc levelOne, mkLevelParam `w, mkLevelSucc (mkLevelParam `x)]
#eval toString $ normalize $ mkLevelMax levelZero (mkLevelParam `x)
#eval toString $ normalize $ mkLevelMax (mkLevelParam `x) levelZero
#eval toString $ normalize $ mkLevelMax levelZero levelOne
#eval toString $ normalize $ mkLevelSucc (mkLevelMax (mkLevelParam `x) (mkLevelParam `x))
#eval toString $ normalize $ mkLevelMax (mkLevelIMax (mkLevelParam `x) levelOne) (mkLevelMax (mkLevelSucc (mkLevelParam `x)) (mkLevelParam `x))
#eval toString $ normalize $ mkLevelIMax (mkLevelIMax (mkLevelParam `x) levelOne) (mkLevelMax (mkLevelSucc (mkLevelParam `x)) (mkLevelParam `x))
#eval toString $ #[levelZero, mkLevelSucc (mkLevelSucc (mkLevelParam `z)), levelOne, mkLevelSucc (mkLevelSucc (mkLevelParam `x)), levelZero, mkLevelParam `x, mkLevelParam `y, mkLevelParam `x, mkLevelParam `z, mkLevelSucc (mkLevelParam `x)].qsort normLt

end Level
end Lean

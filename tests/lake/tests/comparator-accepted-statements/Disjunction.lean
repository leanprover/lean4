module

public import Accepted

/-! Disjunction is not a combination of individually accepted hypotheses. -/

public theorem task (_ : Or Accepted.first Accepted.second) : True := True.intro

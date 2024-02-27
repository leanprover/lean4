inductive Term where
 | const : String → Term
 | app   : String → List Term → Term

namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs

  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

derive_functional_induction replaceConst

theorem numConsts_replaceConst (a b : String) (e : Term) : numConsts (replaceConst a b e) = numConsts e := by
  apply replaceConst.induct
    (motive1 := fun e => numConsts (replaceConst a b e) = numConsts e)
    (motive2 := fun es =>  numConstsLst (replaceConstLst a b es) = numConstsLst es)
  case case1 => intro c h; guard_hyp h :ₛ (a == c) = true; simp [replaceConst, numConsts, *]
  case case2 => intro c h; guard_hyp h :ₛ ¬(a == c) = true; simp [replaceConst, numConsts, *]
  case case3 =>
    intros f cs ih
    guard_hyp ih :ₛnumConstsLst (replaceConstLst a b cs) = numConstsLst cs
    simp [replaceConst, numConsts, *]
  case case4 => simp [replaceConstLst, numConstsLst, *]
  case case5 =>
    intro c cs ih₁ ih₂
    guard_hyp ih₁ :ₛ numConsts (replaceConst a b c) = numConsts c
    guard_hyp ih₂ :ₛ numConstsLst (replaceConstLst a b cs) = numConstsLst cs
    simp [replaceConstLst, numConstsLst, *]

theorem numConsts_replaceConst' (a b : String) (e : Term) : numConsts (replaceConst a b e) = numConsts e := by
  apply replaceConst.induct
    (motive1 := fun e => numConsts (replaceConst a b e) = numConsts e)
    (motive2 := fun es =>  numConstsLst (replaceConstLst a b es) = numConstsLst es)
  <;> intros <;> simp [replaceConst, numConsts, replaceConstLst, numConstsLst, *]

end Term

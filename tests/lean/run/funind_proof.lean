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
  -- Since #4733 this function can be compiled using structural recursion,
  -- but then the construction of the functional induction principle falls over
  -- TODO: Fix funind, and then omit the `termination_by` here (or test both variants)
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)
  termination_by t => sizeOf t

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
  termination_by ts => sizeOf ts
end


/--
info: Term.replaceConst.induct (a b : String) (motive1 : Term → Prop) (motive2 : List Term → Prop)
  (case1 : ∀ (a_1 : String), (a == a_1) = true → motive1 (const a_1))
  (case2 : ∀ (a_1 : String), ¬(a == a_1) = true → motive1 (const a_1))
  (case3 : ∀ (a : String) (cs : List Term), motive2 cs → motive1 (app a cs)) (case4 : motive2 [])
  (case5 : ∀ (c : Term) (cs : List Term), motive1 c → motive2 cs → motive2 (c :: cs)) (a✝ : Term) : motive1 a✝
-/
#guard_msgs in
#check replaceConst.induct

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

theorem numConsts_replaceConst'' (a b : String) (e : Term) : numConsts (replaceConst a b e) = numConsts e := by
  induction e using replaceConst.induct (a := a) (b := b)
    (motive2 := fun es =>  numConstsLst (replaceConstLst a b es) = numConstsLst es) <;>
    simp [replaceConst, numConsts, replaceConstLst, numConstsLst, *]

end Term

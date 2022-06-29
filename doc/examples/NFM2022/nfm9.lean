/- Mutual recursion -/

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
   | const c => if a = c then const b else const c
   | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
   | [] => []
   | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

/- Mutual recursion in theorems -/

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
            : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
            : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end

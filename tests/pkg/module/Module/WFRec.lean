module

/-!
Defines a recursive function in a way that causes auxillary
theorems to be abstracted out of the embedded termination proofs.
In module `WFRecFunInd` we check whether we can generate the
funind theorem, which may have to unfold these proofs.
-/

@[expose] def ackermann : Nat → Nat → Nat
| 0, m => m+1
| n + 1, 0 => ackermann n 1
| n + 1, m + 1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n,m)

-- The critical abstracted proof is the following, because it abstracts over the
-- induction hypothesis (the `x✝` below)

/--
info: ackermann._unary._proof_5 (n m : Nat)
  (x✝ :
    (y : (_ : Nat) ×' Nat) →
      (invImage (fun x => PSigma.casesOn x fun a a_1 => (a, a_1)) Prod.instWellFoundedRelation).1 y ⟨n.succ, m.succ⟩ →
        Nat) :
  (invImage (fun x => PSigma.casesOn x fun a a_1 => (a, a_1)) Prod.instWellFoundedRelation).1 ⟨n, x✝ ⟨n + 1, m⟩ ⋯⟩
    ⟨n.succ, m.succ⟩
-/
#guard_msgs in
#check ackermann._unary._proof_5

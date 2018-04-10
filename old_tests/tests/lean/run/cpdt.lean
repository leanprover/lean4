/- "Proving in the Large" chapter of CPDT -/

inductive exp : Type
| Const (n : nat) : exp
| Plus (e1 e2 : exp) : exp
| Mult (e1 e2 : exp) : exp

open exp

def eeval : exp → nat
| (Const n)    := n
| (Plus e1 e2) := eeval e1 + eeval e2
| (Mult e1 e2) := eeval e1 * eeval e2

def times (k : nat) : exp → exp
| (Const n)    := Const (k * n)
| (Plus e1 e2) := Plus (times e1) (times e2)
| (Mult e1 e2) := Mult (times e1) e2

def reassoc : exp → exp
| (Const n)    := (Const n)
| (Plus e1 e2) :=
  let e1' := reassoc e1 in
  let e2' := reassoc e2 in
  match e2' with
  | (Plus e21 e22) := Plus (Plus e1' e21) e22
  | _              := Plus e1' e2'
  end
| (Mult e1 e2) :=
  let e1' := reassoc e1 in
  let e2' := reassoc e2 in
  match e2' with
  | (Mult e21 e22) := Mult (Mult e1' e21) e22
  | _              := Mult e1' e2'
  end

attribute [simp] mul_add times reassoc eeval mul_comm mul_assoc mul_left_comm

theorem eeval_times (k e) : eeval (times k e) = k * eeval e :=
by induction e; simp [*]

theorem reassoc_correct (e) : eeval (reassoc e) = eeval e :=
by induction e; simp [*]; cases (reassoc e_e2); rsimp

import tools.mini_crush
/-
This corresponds to Chapter 2 of CPDT, Some Quick Examples
-/
open list

inductive binop : Type
| Plus
| Times

open binop

inductive exp : Type
| Const : nat → exp
| Binop : binop → exp → exp → exp

open exp

def binop_denote : binop → nat → nat → nat
| Plus  := (+)
| Times := (*)

def exp_denote : exp → nat
| (Const n)       := n
| (Binop b e1 e2) := (binop_denote b) (exp_denote e1) (exp_denote e2)

inductive instr : Type
| iConst : ℕ → instr
| iBinop : binop → instr

open instr

@[reducible]
def prog := list instr
def stack := list nat

def instr_denote (i : instr) (s : stack) : option stack :=
match i with
| (iConst n) := some (n :: s)
| (iBinop b) :=
  match s with
  | (arg1 :: arg2 :: s') := some ((binop_denote b) arg1 arg2 :: s')
  | _                    := none
  end
end

def prog_denote : prog → stack → option stack
| nil       s := some s
| (i :: p') s :=
  match instr_denote i s with
  | none := none
  | (some s') := prog_denote p' s'
  end

def compile : exp → prog
| (Const n)       := iConst n :: nil
| (Binop b e1 e2) := compile e2 ++ compile e1 ++ iBinop b :: nil

/- This example needs a few facts from the list library. -/

@[simp] lemma compile_correct' :
  ∀ e p s, prog_denote (compile e ++ p) s = prog_denote p (exp_denote e :: s) :=
by mini_crush

@[simp] lemma compile_correct : ∀ e, prog_denote (compile e) nil = some (exp_denote e :: nil) :=
by mini_crush

inductive type : Type
| Nat
| Bool

open type

inductive tbinop : type → type → type → Type
| TPlus  : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq    : ∀ t, tbinop t t Bool
| TLt    : tbinop Nat Nat Bool

open tbinop

inductive texp : type → Type
| TNConst : nat → texp Nat
| TBConst : bool → texp Bool
| TBinop  : ∀ {t1 t2 t}, tbinop t1 t2 t → texp t1 → texp t2 → texp t

open texp

def type_denote : type → Type
| Nat  := nat
| Bool := bool

/- To simulate CPDT we need the next three operations. -/

def beq_nat (m n : ℕ) : bool := if m = n then tt else ff
def eqb (b₁ b₂ : bool) : bool := if b₁ = b₂ then tt else ff
def leb (m n : ℕ) : bool := if m < n then tt else ff

def tbinop_denote : Π {arg1 arg2 res : type},
  tbinop arg1 arg2 res → type_denote arg1 → type_denote arg2 → type_denote res
| ._ ._ ._ TPlus      := ((+) : ℕ → ℕ → ℕ)
| ._ ._ ._ TTimes     := ((*) : ℕ → ℕ → ℕ)
| ._ ._ ._ (TEq Nat)  := beq_nat
| ._ ._ ._ (TEq Bool) := eqb
| ._ ._ ._ TLt        := leb

def texp_denote : Π {t : type}, texp t → type_denote t
| ._ (TNConst n)             := n
| ._ (TBConst b)             := b
| ._ (@TBinop _ _ _ b e1 e2) := (tbinop_denote b) (texp_denote e1) (texp_denote e2)

@[reducible]
def tstack := list type

inductive tinstr : tstack → tstack → Type
| TiNConst : Π s, nat → tinstr s (Nat :: s)
| TiBConst : Π s, bool → tinstr s (Bool :: s)
| TiBinop  : Π {arg1 arg2 res s}, tbinop arg1 arg2 res → tinstr (arg1 :: arg2 :: s) (res :: s)

open tinstr

inductive tprog : tstack → tstack → Type
| TNil  : Π {s}, tprog s s
| TCons : Π {s1 s2 s3}, tinstr s1 s2 → tprog s2 s3 → tprog s1 s3

open tprog

def vstack : tstack → Type
| nil        := unit
| (t :: ts') := type_denote t × vstack ts'

def tinstr_denote : Π {ts ts' : tstack}, tinstr ts ts' → vstack ts → vstack ts'
| ._ ._ (TiNConst ts n)              := λ s, (n, s)
| ._ ._ (TiBConst ts b)              := λ s, (b, s)
| ._ ._ (@TiBinop arg1 arg2 res s b) := λ ⟨arg1, ⟨arg2, s'⟩⟩, ((tbinop_denote b) arg1 arg2, s')

def tprog_denote : Π {ts ts' : tstack}, tprog ts ts' → vstack ts → vstack ts'
| ._ ._ (@TNil _)           := λ s, s
| ._ ._ (@TCons _ _ _ i p') := λ s, tprog_denote p' (tinstr_denote i s)

def tconcat : Π {ts ts' ts'' : tstack}, tprog ts ts' → tprog ts' ts'' → tprog ts ts''
| ._ ._ ts'' (@TNil _) p'           := p'
| ._ ._ ts'' (@TCons _ _ _ i p1) p' := TCons i (tconcat p1 p')

def tcompile : Π {t : type}, texp t → Π ts : tstack, tprog ts (t :: ts)
| ._ (TNConst n) ts             := TCons (TiNConst _ n) TNil
| ._ (TBConst b) ts             := TCons (TiBConst _ b) TNil
| ._ (@TBinop _ _ _ b e1 e2) ts := tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TiBinop b) TNil))

@[simp] lemma tconcat_correct : ∀ ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts),
  tprog_denote (tconcat p p') s = tprog_denote p' (tprog_denote p s) :=
by mini_crush

@[simp] lemma tcompile_correct' : ∀ t (e : texp t) ts (s : vstack ts),
  tprog_denote (tcompile e ts) s = (texp_denote e, s) :=
by mini_crush

lemma tcompile_correct :
  ∀ t (e : texp t), tprog_denote (tcompile e nil) () = (texp_denote e, ()) :=
by mini_crush

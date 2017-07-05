lemma nat.lt_add_of_lt {a b c : nat} : a < b → a < c + b :=
begin
  intro h,
  have aux₁ := nat.le_add_right b c,
  have aux₂ := lt_of_lt_of_le h aux₁,
  rwa [add_comm] at aux₂
end

lemma nat.lt_one_add_of_lt {a b : nat} : a < b → a < 1 + b :=
begin
  intro h,
  have aux := lt.trans h (nat.lt_succ_self _),
  rwa [<- nat.add_one_eq_succ, add_comm] at aux
end

namespace list
def attach_aux {α} (l : list α) : Π (c : list α), (∀ x : α, x ∈ c → x ∈ l) → list {a : α // a ∈ l}
| []      h := []
| (a::as) h :=
  ⟨a, h a (list.mem_cons_self _ _)⟩ :: attach_aux as (λ x hin, h x (list.mem_cons_of_mem _ hin))

def attach {α} (l : list α) : list {a : α // a ∈ l} :=
attach_aux l l (λ x h, h)

open well_founded_tactics

lemma sizeof_lt_sizeof_of_mem {α} [has_sizeof α] {a : α} : ∀ {l : list α}, a ∈ l → sizeof a < sizeof l
| []      h := absurd h (not_mem_nil _)
| (b::bs) h :=
  begin
    cases eq_or_mem_of_mem_cons h with h_1 h_2,
    subst h_1,
    {unfold_sizeof, cancel_nat_add_lt, trivial_nat_lt},
    {have aux₁ := sizeof_lt_sizeof_of_mem h_2,
     unfold_sizeof,
     exact nat.lt_one_add_of_lt (nat.lt_add_of_lt aux₁)}
  end
end list

inductive term
| const : string → term
| app   : string → list term → term

def num_consts : term → nat
| (term.const n)  := 1
| (term.app n ts) :=
  ts.attach.foldl
   (λ r p,
     have sizeof p.1 < n.length + (1 + sizeof ts), from
       calc sizeof p.1 < 1 + (n.length + sizeof ts) : nat.lt_one_add_of_lt (nat.lt_add_of_lt (list.sizeof_lt_sizeof_of_mem p.2))
                 ...   = n.length + (1 + sizeof ts) : by simp,
     r + num_consts p.1)
   0

#eval num_consts (term.app "f" [term.const "x", term.app "g" [term.const "x", term.const "y"]])

#check num_consts.equations._eqn_2

def num_consts' : term → nat
| (term.const n)  := 1
| (term.app n ts) :=
  ts.attach.foldl
   (λ r ⟨t, h⟩,
     have sizeof t < n.length + (1 + sizeof ts), from
       calc sizeof t < 1 + (n.length + sizeof ts) : nat.lt_one_add_of_lt (nat.lt_add_of_lt (list.sizeof_lt_sizeof_of_mem h))
                 ... = n.length + (1 + sizeof ts) : by simp,
     r + num_consts' t)
   0

#check num_consts'.equations._eqn_2

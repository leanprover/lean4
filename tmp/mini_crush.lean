declare_trace mini_crush

namespace mini_crush
open smt_tactic tactic

/- Collect relevant functions -/
meta def is_auto_construction : name → bool
| (name.mk_string "brec_on" p)      := tt
| (name.mk_string "cases_on" p)     := tt
| (name.mk_string "rec_on" p)       := tt
| (name.mk_string "no_confusion" p) := tt
| (name.mk_string "below" p)        := tt
| _                                 := ff

meta def is_relevant_fn (n : name) : tactic bool :=
do env ← get_env,
   if ¬env^.is_definition n ∨ is_auto_construction n then return ff
   else if env^.in_current_file n then return tt
   else in_open_namespaces n

meta def collect_revelant_fns_aux : name_set → expr → tactic name_set
| s e :=
e^.mfold s $ λ t _ s,
  match t with
  | expr.const c _ :=
    if s^.contains c then return s
    else mcond (is_relevant_fn c)
      (do new_s ← return $ if c^.is_internal then s else s^.insert c,
          d     ← get_decl c,
          collect_revelant_fns_aux new_s d^.value)
      (return s)
  | _              := return s
  end

meta def collect_revelant_fns : tactic name_set :=
do ctx ← local_context,
   s₁  ← mfoldl (λ s e, infer_type e >>= collect_revelant_fns_aux s) mk_name_set ctx,
   target >>= collect_revelant_fns_aux s₁

/- repeat simp & intro -/

meta def simph_and_intro_aux : simp_lemmas → tactic unit
| S := do
  t ← target,


return ()

meta def simph_and_intro : tactic unit :=
do S ← simp_lemmas.mk_default,
   S ← collect_ctx_simps >>= S^.append,
   simph_and_intro_aux S


meta def collect_ctx_simps : tactic (list expr) :=


meta def size (e : expr) : nat :=
e^.fold 1 (λ e _ n, n+1)

structure config :=
(num_rounds := 5)
(max_depth  := 2)
(timeout    := 10000)

meta def close_easy (cfg : config) : smt_tactic unit :=
all_goals (repeat_at_most cfg^.num_rounds (ematch >> try close))

meta def destruct_and_close (cfg : config) (e : expr) : smt_tactic unit :=
destruct e >> close_easy cfg

meta def induction_and_close (cfg : config) (e : expr) : smt_tactic unit :=
smt_tactic.induction e >> close_easy cfg

open expr tactic

meta def is_inductive (e : expr) : tactic bool :=
do type ← infer_type e,
   C    ← return type^.get_app_fn,
   env  ← get_env,
   return $ C^.is_constant && env^.is_inductive C^.const_name

open monad

meta def collect_inductive_aux : expr_set → expr → tactic expr_set
| S e :=
  if S^.contains e then return S
  else do
    new_S ← cond (is_inductive e) (return $ S^.insert e) (return S),
    if e^.is_app
    then fold_explicit_args e new_S collect_inductive_aux
    else return new_S

meta def collect_inductive : expr → tactic expr_set :=
collect_inductive_aux mk_expr_set

meta def collect_inductive_from_target_aux : tactic (list expr) :=
do S ← target >>= collect_inductive,
   return $ list.qsort (λ e₁ e₂, size e₁ < size e₂) $ S^.to_list

meta def collect_inductive_from_target : smt_tactic (list expr) :=
collect_inductive_from_target_aux

meta def snapshot := smt_state × tactic_state

meta def save : smt_tactic snapshot :=
smt_tactic.read

meta def restore : snapshot → smt_tactic unit :=
smt_tactic.write

open smt_tactic

meta def rsimp_target : smt_tactic unit :=
do ccs ← to_cc_state,
   rsimp.rsimplify_goal ccs

meta def try_snapshots {α} (cont : α → smt_tactic unit) : list (α × snapshot) → smt_tactic unit
| []           := failed
| ((a, s)::ss) := (restore s >> cont a) <|> try_snapshots ss

meta def search {α} (max_depth : nat) (act : nat → α → smt_tactic (list (α × snapshot))) : nat → α → smt_tactic unit
| n s := do
  all_goals $ try intros >> try close,
  now
  <|>
  if n > max_depth then trace "max depth reached" >> trace_state >> failed
  else all_goals $ try intros >> act n s >>= try_snapshots (search (n+1))

meta def init_lemmas : smt_tactic unit :=
do /- Add equational lemmas for relevant functions -/
   fns ← collect_revelant_fns,
   mfor' fns^.to_list add_ematch_eqn_lemmas_for,
   /- Add [rsimp] lemmas -/
   get_hinst_lemmas_for_attr `rsimp_attr >>= add_lemmas

meta def try_induction_aux (hs : hinst_lemmas) (cont : smt_tactic unit) : list expr → smt_tactic unit
| []      := failed
| (e::es) := (induction e >> all_goals (set_lemmas hs >> try intros >> cont >> now)) <|> try_induction_aux es

meta def try_induction (hs : hinst_lemmas) (cont : smt_tactic unit) : smt_tactic unit :=
collect_inductive_from_target >>= mfilter (λ e, return $ e^.is_local_constant) >>= try_induction_aux hs cont

meta def mini_crush_1 (cfg : config := {}) : tactic unit :=
using_smt $ do
  init_lemmas, hs ← get_lemmas,
  close_easy cfg,
  now
  <|>
  try_induction hs (close_easy cfg)

universe variable u

export nat (succ)

def is_zero : ℕ → bool
| 0        := tt
| (succ _) := ff

def plus : ℕ → ℕ → ℕ
| 0 m         := m
| (succ n') m := succ (plus n' m)

def times : ℕ → ℕ → ℕ
| 0        m := m
| (succ n) m := plus m (times n m)

@[simp] theorem n_plus_0 (n : ℕ) : plus n 0 = n :=
by mini_crush_1

@[simp] theorem plus_assoc (n1 n2 n3 : nat) : plus (plus n1 n2) n3 = plus n1 (plus n2 n3) :=
by mini_crush_1

inductive nat_list : Type
| NNil  : nat_list
| NCons : nat → nat_list → nat_list

open nat_list

def nlength : nat_list → ℕ
| NNil          := 0
| (NCons _ ls') := succ (nlength ls')

def napp : nat_list → nat_list → nat_list
| NNil ls2 := ls2
| (NCons n ls1') ls2 := NCons n (napp ls1' ls2)

theorem nlength_napp (ls1 ls2 : nat_list) : nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2) :=
by mini_crush_1

inductive nat_btree : Type
| NLeaf : nat_btree
| NNode : nat_btree → ℕ → nat_btree → nat_btree

open nat_btree

def nsize : nat_btree → ℕ
| NLeaf             := succ 0
| (NNode tr1 _ tr2) := plus (nsize tr1) (nsize tr2)

def nsplice : nat_btree → nat_btree → nat_btree
| NLeaf tr2               := NNode tr2 0 NLeaf
| (NNode tr1' n tr2') tr2 := NNode (nsplice tr1' tr2) n tr2'

theorem nsize_nsplice (tr1 tr2 : nat_btree) : nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1) :=
by mini_crush_1

inductive formula : Type
| Eq     : nat → nat → formula
| And    : formula → formula → formula
| Forall : (nat → formula) → formula

open formula

example forall_refl : formula := Forall (λ x, Eq x x)

def formula_denote : formula → Prop
| (Eq n1 n2)  := n1 = n2
| (And f1 f2) := formula_denote f1 ∧ formula_denote f2
| (Forall f') := ∀ n : nat, formula_denote (f' n)

def swapper : formula → formula
| (Eq n1 n2)  := Eq n2 n1
| (And f1 f2) := And (swapper f2) (swapper f1)
| (Forall f') := Forall (λ n, swapper (f' n))

attribute [simp] formula_denote swapper

theorem swapper_preserves_truth (f) : formula_denote f → formula_denote (swapper f) :=
by induction f; simph; intros; rsimp

exit
begin [smt] induction f, admit, admit, intros, init_lemmas, add_lemmas_from_facts, eblast, rsimp_target, intros, eblast, rsimp_target end

exit

begin [smt]
  induction ls1,
  init_lemmas, eblast

end






exit

  (intros >> close >> now)
  <|>
  (if n > max_depth then (trace "max depth reached" >> rsimp >> trace_state)
   else all_goals $ intros )


exit
    smt_tactic.intros >> collect_inductive_from_target >>= try_destruct cfg >>= try_snapshots (search (n+1))



meta def try_and_save {α} (t : smt_tactic α) : smt_tactic (option (α × nat × snapshot)) :=
do {
  s     ← save,
  a     ← t,
  new_s ← save,
  n     ← num_goals,
  restore s,
  return (a, n, new_s)
} <|> return none

meta def try_all_aux {α} (ts : α → smt_tactic unit) : list α → list (α × nat × snapshot) → smt_tactic (list (α × nat × snapshot))
| []      [] := failed
| []      rs := return rs^.reverse
| (v::vs) rs := do
  r ← try_and_save (ts v),
  match r with
  | some (_, 0, s) := return [(v, 0, s)]
  | some (_, n, s) := try_all_aux vs ((v, n, s)::rs)
  | none           := try_all_aux vs rs
  end

meta def try_all {α} (ts : α → smt_tactic unit) (vs : list α) : smt_tactic (list (α × nat × snapshot)) :=
try_all_aux ts vs []

meta def sort_snapshots (rs : list (expr × nat × snapshot)) : list snapshot :=
let ss := flip list.qsort rs $ λ ⟨e₁, n₁, _⟩ ⟨e₂, n₂, _⟩, if n₁ ≠ n₂ then n₁ < n₂ else size e₁ < size e₂ in
ss^.for $ λ ⟨_, _, s⟩, s

meta def try_destruct (cfg : config) (es : list expr) : smt_tactic (list snapshot) :=
sort_snapshots <$> try_all (destruct_and_close cfg) es

meta def try_induction (cfg : config) (es : list expr) : smt_tactic (list snapshot) :=
sort_snapshots <$> try_all (induction_and_close cfg) es

meta def try_snapshots {α} (cont : smt_tactic α) : list snapshot → smt_tactic α
| []      := failed
| (s::ss) := (restore s >> cont) <|> try_snapshots ss

meta def search (cfg : config) : nat → smt_tactic unit
| n :=
  close >> now
  <|>
  if n > cfg^.max_depth then trace "max depth reached" >> rsimp >> trace_state
  else all_goals $
    smt_tactic.intros >> collect_inductive_from_target >>= try_destruct cfg >>= try_snapshots (search (n+1))

meta def with_smt (t : smt_tactic unit) : tactic unit :=
using_smt_with {em_attr := `rsimp_attr} t

meta def strategy_1 (cfg : config := {}) : tactic unit :=
try_for cfg^.timeout (try simph >> try intros >> try simph >> try contradiction >> now)

meta def strategy_2 (cfg : config := {}) : tactic unit :=
try_for cfg^.timeout $ with_smt $
  collect_inductive_from_target >>= try_induction cfg >>=
  try_snapshots (all_goals $
    trace "------------" >> trace_state >> now)

-- exit
--  try close >> try simph >> try intros >> try simph >>  try contradiction >> now)

meta def strategy_3 (cfg : config := {}) : tactic unit :=
try_for cfg^.timeout $ with_smt $
  collect_inductive_from_target >>= try_induction cfg >>=
  try_snapshots (all_goals $
     trace "------------" >> trace_state >> trace "--------" >>
     try close >> try (search cfg 1))

meta def main (cfg : config := {}) : tactic unit :=
strategy_2 <|> strategy_3

end mini_crush

meta def mini_crush := mini_crush.main

universe variable u

export nat (succ)

def is_zero : ℕ → bool
| 0        := tt
| (succ _) := ff

def plus : ℕ → ℕ → ℕ
| 0 m         := m
| (succ n') m := succ (plus n' m)

def times : ℕ → ℕ → ℕ
| 0        m := m
| (succ n) m := plus m (times n m)

attribute [simp] is_zero plus

set_option trace.smt.ematch true

theorem n_plus_0 (n : ℕ) : plus n 0 = n :=
by mini_crush.strategy_3

exit

inductive nat_list : Type
| NNil  : nat_list
| NCons : nat → nat_list → nat_list

open nat_list

def nlength : nat_list → ℕ
| NNil          := 0
| (NCons _ ls') := succ (nlength ls')

def napp : nat_list → nat_list → nat_list
| NNil ls2 := ls2
| (NCons n ls1') ls2 := NCons n (napp ls1' ls2)

attribute [simp] nlength napp

theorem nlength_napp (ls1 ls2 : nat_list) : nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2) :=
by induction ls1; rsimp

inductive nat_btree : Type
| NLeaf : nat_btree
| NNode : nat_btree → ℕ → nat_btree → nat_btree

open nat_btree

def nsize : nat_btree → ℕ
| NLeaf             := succ 0
| (NNode tr1 _ tr2) := plus (nsize tr1) (nsize tr2)

def nsplice : nat_btree → nat_btree → nat_btree
| NLeaf tr2               := NNode tr2 0 NLeaf
| (NNode tr1' n tr2') tr2 := NNode (nsplice tr1' tr2) n tr2'

attribute [simp] nsize nsplice

theorem plus_assoc (n1 n2 n3 : nat) : plus (plus n1 n2) n3 = plus n1 (plus n2 n3) :=
by induction n1; simph

attribute [simp] n_plus_0 plus_assoc

theorem nsize_nsplice (tr1 tr2 : nat_btree) : nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1) :=
by induction tr1; simph

export list (nil cons)

def length {α : Type u} : list α → ℕ
| nil          := 0
| (cons _ ls') := succ (length ls')

def app {α : Type u} : list α → list α → list α
| nil ls2           := ls2
| (cons x ls1') ls2 := cons x (app ls1' ls2)

attribute [simp] length app

theorem length_app {α : Type u} (ls1 ls2 : list α) : length (app ls1 ls2) = plus (length ls1) (length ls2) :=
by induction ls1; simph


inductive pformula : Type
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula → pformula → pformula.

open pformula

def pformula_denote : pformula → Prop
| Truth               := true
| Falsehood           := false
| (Conjunction f1 f2) := pformula_denote f1 ∧ pformula_denote f2

attribute [simp] pformula_denote

open pformula

inductive formula : Type
| Eq     : nat → nat → formula
| And    : formula → formula → formula
| Forall : (nat → formula) → formula

open formula

example forall_refl : formula := Forall (λ x, Eq x x)

def formula_denote : formula → Prop
| (Eq n1 n2)  := n1 = n2
| (And f1 f2) := formula_denote f1 ∧ formula_denote f2
| (Forall f') := ∀ n : nat, formula_denote (f' n)

def swapper : formula → formula
| (Eq n1 n2)  := Eq n2 n1
| (And f1 f2) := And (swapper f2) (swapper f1)
| (Forall f') := Forall (λ n, swapper (f' n))

attribute [simp] formula_denote swapper

theorem swapper_preserves_truth (f) : formula_denote f → formula_denote (swapper f) :=
begin
  (do s ← mini_crush.collect_revelant_fns, tactic.trace s^.to_list),
  induction f; intro h; simp at h; simph; intros; rsimp

end

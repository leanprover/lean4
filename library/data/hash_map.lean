/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.list.set data.list.comb init.data.array data.pnat

universes u v w

def bucket_array (α : Type u) (β : α → Type v) (n : ℕ+) :=
array (list Σ a, β a) n.1

def hash_map.mk_idx (n : ℕ+) (i : nat) : fin n.1 :=
⟨i % n.1, nat.mod_lt _ n.2⟩

namespace bucket_array
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)
variables {n : ℕ+} (data : bucket_array α β n)

def read (a : α) : list Σ a, β a :=
let bidx := hash_map.mk_idx n (hash_fn a) in
data.read bidx

def write (hash_fn : α → nat) (a : α) (l : list Σ a, β a) : bucket_array α β n :=
let bidx := hash_map.mk_idx n (hash_fn a) in
data.write bidx l

def modify (hash_fn : α → nat) (a : α) (f : list (Σ a, β a) → list (Σ a, β a)) : bucket_array α β n :=
let bidx := hash_map.mk_idx n (hash_fn a) in
array.write data bidx (f (array.read data bidx))

def as_list : list Σ a, β a :=
data.foldl [] (λbkt r, r ++ bkt)

theorem mem_as_list (a : Σ a, β a) : a ∈ data.as_list ↔ ∃i, a ∈ array.read data i :=
suffices ∀j h, a ∈ array.iterate_aux data (λ_ bkt r, r ++ bkt) j h [] ↔
  ∃ (i : fin n.1), i.1 < j ∧ a ∈ array.read data i, from
iff.trans (this _ _) (exists_congr $ λi, and_iff_right i.2),
begin
  intros,
  induction j with j IH,
  exact ⟨false.elim, λ⟨i, h, _⟩, absurd h (nat.not_lt_zero _)⟩,
  have IH := IH (le_of_lt h),
  simp[array.iterate_aux],
  exact ⟨λo, or.elim o
    (λm, ⟨⟨j, h⟩, nat.le_refl _, m⟩)
    (λm, let ⟨i, il, im⟩ := IH.1 m in ⟨i, nat.le_succ_of_le il, im⟩),
  λ⟨i, le, m⟩, or.elim (lt_or_eq_of_le (nat.le_of_succ_le_succ le))
    (λl, or.inr (IH.2 ⟨i, l, m⟩))
    (λe, or.inl $ by rwa [← show i = ⟨j, h⟩, from fin.eq_of_veq e])⟩
end

def foldl {δ : Type w} (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.foldl d (λ b d, b.foldl (λ r a, f r a.1 a.2) d)

lemma foldl_eq_lem {γ : Type u} {δ : Type w} (d : δ) (f : δ → γ → δ) : Π l : list (list γ),
  l.foldr (λ (b:list γ) d, b.foldl f d) d = (l.foldr (λ(bkt r : list γ), r ++ bkt) []).foldl f d
| []      := rfl
| (l::ls) := show l.foldl f (ls.foldr (λ (b:list γ) d, b.foldl f d) d) =
  (ls.foldr (λ (bkt r : list γ), r ++ bkt) [] ++ l).foldl f d, by rw [list.append_foldl, foldl_eq_lem ls]

theorem foldl_eq {δ : Type w} (d : δ) (f : δ → Π a, β a → δ) :
  data.foldl d f = data.as_list.foldl (λ r a, f r a.1 a.2) d :=
let f' : δ → (Σ a, β a) → δ := λ r a, f r a.1 a.2 in
let g : list (Σ a, β a) → δ → δ := λ b d, b.foldl f' d in
calc array.foldl data d g = data.rev_list.foldr g d : data.foldl_eq d g
   ... = (data.rev_list.foldr (λ(bkt r : list (Σa, β a)), r ++ bkt) []).foldl f' d : foldl_eq_lem _ _ _
   ... = (array.foldl data [] (λbkt r, r ++ bkt)).foldl f' d : by rw array.foldl_eq data [] (λbkt r, r ++ bkt)
end
end bucket_array

namespace hash_map
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)

def reinsert_aux {n} (data : bucket_array α β n) (a : α) (b : β a) : bucket_array α β n :=
data.modify hash_fn a (λl, ⟨a, b⟩ :: l)

parameter [decidable_eq α]

def find_aux (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) := if h : a' = a then some (eq.rec_on h b) else find_aux t

theorem find_aux_iff (a : α) (b : β a) : Π (l : list Σ a, β a), (l.map sigma.fst).nodup → (find_aux a l = some b ↔ sigma.mk a b ∈ l)
| []          nd := ⟨λn, by contradiction, false.elim⟩
| (⟨a',b'⟩::t) nd := by simp[find_aux]; exact
  if h : a' = a then by rw dif_pos h; exact
    match a', b', h with ._, b', rfl :=
      ⟨λe, by injection e with e; rw ← e; exact or.inl rfl,
       λo, or.elim o
         (λe, by injection e with _ e; rw eq_of_heq e)
         (λm, have a' ∉ t.map sigma.fst, from list.not_mem_of_nodup_cons nd,
              by rw h at this; exact absurd (list.mem_map sigma.fst m) this)⟩
    end
  else by rw dif_neg h; exact iff.trans (find_aux_iff t $ list.nodup_of_nodup_cons nd)
    (iff.symm $ or_iff_right_of_imp (λn, by injection n with aa _; rw aa at h; contradiction))

def contains_aux (a : α) (l : list Σ a, β a) : bool :=
(find_aux a l).is_some

theorem contains_aux_iff (a : α) (l : list Σ a, β a) (nd : (l.map sigma.fst).nodup) : (contains_aux a l ↔ a ∈ l.map sigma.fst) :=
begin
  delta contains_aux,
  ginduction find_aux a l with h b,
  refine ⟨λn, by contradiction, λm, _⟩,
  exact
    let ⟨⟨a', b⟩, m, e⟩ := list.exists_of_mem_map m in
    match a', b, m, e with ._, b, m, rfl :=
      by rw ((find_aux_iff a b l nd).2 m) at h; contradiction end,
  exact ⟨λ_, list.mem_map _ ((find_aux_iff a b l nd).1 h), λ_, dec_trivial⟩,
end

def replace_aux (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replace_aux t

def erase_aux (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: erase_aux t

inductive valid_aux {α : Type u} {β : α → Type v} (idx : α → nat) : Π (l : list (list Σ a, β a)) (sz : nat), Prop
| nil {} : valid_aux [] 0
| cons : Π (c : list Σ a, β a) {l sz}, valid_aux l sz → (c.map sigma.fst).nodup →
  (∀ a ∈ c, idx (sigma.fst a) = l.length) → valid_aux (c::l) (sz + c.length)

theorem valid_aux.unfold_cons {idx : α → nat} : Π {c l sz}, valid_aux idx (c::l) sz →
  ∃ sz', valid_aux idx l sz' ∧ (c.map sigma.fst).nodup ∧ (∀ a ∈ c, idx (sigma.fst a) = l.length) ∧ sz = sz' + c.length
| ._ ._ ._ (@valid_aux.cons ._ ._ ._ c l sz' v nd e) := ⟨sz', v, nd, e, rfl⟩

theorem valid_aux.nodup {idx : α → nat} : Π {l : list (list Σ a, β a)} {sz : nat}, valid_aux idx l sz →
  ∀ ⦃c : list Σ a, β a⦄, c ∈ l → (c.map sigma.fst).nodup
| ._ ._ valid_aux.nil                            c' cl := false.elim cl
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) c' cl := or.elim cl (λe, by rwa e) (λm : c' ∈ l, valid_aux.nodup v m)

theorem valid_aux.eq {idx : α → nat} : Π {l : list (list Σ a, β a)} {sz : nat}, valid_aux idx l sz →
  ∀ {i h a b}, sigma.mk a b ∈ l.nth_le i h → idx a = l.length - 1 - i
| ._ ._ valid_aux.nil                            i     h _ _ _  := absurd h (nat.not_lt_zero _)
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) 0     h a b el := e ⟨a, b⟩ el
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) (i+1) h a b el :=
  have idx a = list.length l - 1 - i, from valid_aux.eq v el,
  by rwa [nat.sub_sub, nat.add_comm] at this

theorem valid_aux.insert_lemma1 {idx : α → nat} : Π {l : list (list Σ a, β a)} {sz : nat}, valid_aux idx l sz →
  ∀ {i h a b}, sigma.mk a b ∈ l.nth_le i h → idx a = l.length - 1 - i
| ._ ._ valid_aux.nil                            i     h _ _ _  := absurd h (nat.not_lt_zero _)
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) 0     h a b el := e ⟨a, b⟩ el
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) (i+1) h a b el :=
  have idx a = list.length l - 1 - i, from valid_aux.eq v el,
  by rwa [nat.sub_sub, nat.add_comm] at this

def valid {n} (bkts : bucket_array α β n) (sz : nat) : Prop :=
valid_aux (λa, (mk_idx n (hash_fn a)).1) bkts.rev_list sz

theorem valid.nodup {n} {bkts : bucket_array α β n} {sz : nat} : valid bkts sz → ∀i, ((array.read bkts i).map sigma.fst).nodup :=
λv i, valid_aux.nodup v ((bkts.mem_iff_rev_list_mem _).1 (bkts.read_mem i))

theorem valid.eq {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
 {i h a b} (el : sigma.mk a b ∈ array.read bkts ⟨i, h⟩) : (mk_idx n (hash_fn a)).1 = i :=
have h1 : list.length (array.to_list bkts) - 1 - i < list.length (list.reverse (array.to_list bkts)),
  by simp [*, array.to_list_length, nat.sub_one_sub_lt],
  have _, from nat.sub_eq_sub_min,
have sigma.mk a b ∈ list.nth_le (array.to_list bkts) i (by simp [*, array.to_list_length]), by {rw array.to_list_nth, exact el},
begin
  rw [← list.nth_le_reverse] at this,
  have v : valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.to_list bkts).reverse sz,
  rw array.to_list_reverse,
  exact v,
  have mm := @_root_.hash_map.valid_aux.eq _ _ _ _ _ _ v -- TODO (Mario): Why is explicit namespacing needed here?
    (list.length (array.to_list bkts) - 1 - i) h1 a b this,
  rwa [list.length_reverse, array.to_list_length, nat.sub_sub_self (show i ≤ n.1 - 1, from nat.pred_le_pred h)] at mm
end

theorem valid.eq' {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
 {i a b} (el : sigma.mk a b ∈ array.read bkts i) : mk_idx n (hash_fn a) = i :=
fin.eq_of_veq (match i, el with ⟨j, h⟩, el := v.eq _ el end)

theorem valid.as_list_nodup {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) : (bkts.as_list.map sigma.fst).nodup :=
suffices ∀i h, ((bkts.iterate_aux (λ _ bkt r, r ++ bkt) i h []).map sigma.fst).nodup ∧
  ∀a, a ∈ bkts.iterate_aux (λ _ bkt r, r ++ bkt) i h [] → (mk_idx n (hash_fn a.1)).1 < i, from (this n.1 (le_refl _)).left,
begin
  intros,
  induction i with i IH,
  exact ⟨list.nodup.ndnil, λ_, false.elim⟩,
  simp[array.iterate_aux, list.map_append], exact
  let ⟨nd, al⟩ := IH (le_of_lt h) in
  ⟨ list.nodup_append_of_nodup_of_nodup_of_disjoint nd (v.nodup _ _) $ λa m1 m2,
    let ⟨⟨a', b⟩, m1, e1⟩ := list.exists_of_mem_map m1 in
    let ⟨⟨a'', b'⟩, m2, e2⟩ := list.exists_of_mem_map m2 in
    match a', a'', b, b', m1, m2, e1, e2 with ._, ._, b, b', m1, m2, rfl, rfl :=
      by {have hlt := al _ m1, rw v.eq _ m2 at hlt, exact lt_irrefl _ hlt}
    end,
  λ⟨a, b⟩ m, or.elim m
    (λm2, by rw v.eq _ m2; exact nat.le_refl _)
    (λm1, nat.le_succ_of_le (al _ m1))⟩
end

theorem valid.as_list_length {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) : bkts.as_list.length = sz :=
have ∀l sz, valid_aux (λ (a : α), (mk_idx n (hash_fn a)).val) l sz → ∀t, (l.foldr (λbkt r, r ++ bkt) t).length = sz + t.length,
by {intros, induction a, simp[list.foldr], simp[list.foldr, ih_1]},
by have h := this _ _ v []; rwa [← array.foldl_eq] at h

theorem valid.mk (n : ℕ+) : @valid n (mk_array n.1 []) 0 :=
let bkts : bucket_array α β n := mk_array n.1 [] in
show valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.iterate_aux bkts (λ_ v l, v :: l) n.1 (le_refl n.1) []) 0, from
@nat.rec_on (λi, Πh:i≤n.1, valid_aux (λa, (mk_idx n (hash_fn a)).1)
  (array.iterate_aux bkts (λ_ v l, v :: l) i h []) 0) n.1 (λ_, valid_aux.nil)
  (λi IH h, valid_aux.cons _ (IH (le_of_lt h)) list.nodup.ndnil (λ_, false.elim)) (le_refl _)

theorem valid.find_aux_iff {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) (a : α) (b : β a) :
 find_aux a (bkts.read hash_fn a) = some b ↔ sigma.mk a b ∈ bkts.as_list :=
iff.trans (find_aux_iff _ _ _ (v.nodup _ _))
  $ iff.trans (by exact ⟨λm, ⟨_, m⟩, λ⟨⟨i, h⟩, m⟩, by rwa [← v.eq' _ m] at m⟩)
   (iff.symm (bkts.mem_as_list _))

theorem valid.contains_aux_iff {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) (a : α) :
 contains_aux a (bkts.read hash_fn a) ↔ a ∈ bkts.as_list.map sigma.fst :=
begin
  delta contains_aux,
  ginduction find_aux a (bkts.read hash_fn a) with h b,
  refine ⟨λn, by contradiction, λm, _⟩,
  exact
    let ⟨⟨a', b⟩, m, e⟩ := list.exists_of_mem_map m in
    match a', b, m, e with ._, b, m, rfl :=
      by rw ((v.find_aux_iff _ a b).2 m) at h; contradiction end,
  exact ⟨λ_, list.mem_map _ ((v.find_aux_iff _ a b).1 h), λ_, dec_trivial⟩,
end

theorem mk_as_list (n : ℕ+) : bucket_array.as_list (mk_array n.1 [] : bucket_array α β n) = [] :=
list.eq_nil_of_length_eq_zero ((valid.mk n).as_list_length _)

section
  parameters {n : ℕ+} {bkts : bucket_array α β n}
             {bidx : fin n.1} {f : list (Σ a, β a) → list (Σ a, β a)}
             (u v1 v2 w : list Σ a, β a)

  local notation `L` := array.read bkts bidx
  private def bkts' : bucket_array α β n := array.write bkts bidx (f L)

  theorem valid.modify_aux1 {δ fn} {b : δ} : Π (i) (h : i ≤ n.1) (hb : i ≤ bidx.1),
    array.iterate_aux bkts fn i h b = array.iterate_aux bkts' fn i h b
  | 0     h hb := by simp[array.iterate_aux]
  | (i+1) h (hb : i < bidx.1) := by simp[array.iterate_aux]; exact
    have bn : bidx ≠ ⟨i, h⟩, from λhh, ne_of_lt hb $ fin.veq_of_eq $ eq.symm hh,
    congr (congr_arg (fn _) (show _ = ite (bidx = ⟨i, h⟩) (f _) _, by rw if_neg bn))
      (valid.modify_aux1 i (le_of_lt h) (le_of_lt hb))

  variables (hl : L = u ++ v1 ++ w)
            (hfl : f L = u ++ v2 ++ w)
  include hl hfl

  theorem append_of_modify_aux : Π (i) (h : i ≤ n.1) (hb : i > bidx.1),
    ∃ u' w', array.iterate_aux bkts (λ_ bkt r, r ++ bkt) i h [] = u' ++ v1 ++ w' ∧
             array.iterate_aux bkts' (λ_ bkt r, r ++ bkt) i h [] = u' ++ v2 ++ w'
  | 0     _ hb := absurd hb (nat.not_lt_zero _)
  | (i+1) h hb :=
    match nat.lt_or_eq_of_le $ nat.le_of_succ_le_succ hb with
    | or.inl hl :=
      have bn : bidx ≠ ⟨i, h⟩, from λhh, ne_of_gt hl $ fin.veq_of_eq $ eq.symm hh,
      have he : array.read bkts ⟨i, h⟩ = array.read bkts' ⟨i, h⟩, from
       (show _ = ite (bidx = ⟨i, h⟩) (f _) _, by rw if_neg bn),
      by simp[array.iterate_aux]; rw [← he]; exact
      let ⟨u', w', hb, hb'⟩ := append_of_modify_aux i (le_of_lt h) hl in
      ⟨u', w' ++ array.read bkts ⟨i, h⟩, by simp[hb], by simp[hb']⟩
    | or.inr e :=
      match i, e, h with ._, rfl, h :=
        have array.read bkts' bidx = f L, from
          show ite (bidx = bidx) _ _ = _, by rw if_pos rfl,
        begin
          simp[array.iterate_aux, -add_comm],
          rw [← show bidx = ⟨bidx.1, h⟩, from fin.eq_of_veq rfl],
          refine ⟨array.iterate_aux bkts (λ_ bkt r, r ++ bkt) bidx.1 (le_of_lt h) [] ++ u, w, _⟩,
          rw [← valid.modify_aux1 _ _ (le_refl _)],
          rw [this, hfl, hl],
          simp
        end
      end
    end

  theorem append_of_modify : ∃ u' w', bkts.as_list = u' ++ v1 ++ w' ∧ bkts'.as_list = u' ++ v2 ++ w' :=
  append_of_modify_aux hl hfl _ _ bidx.2

  variables (hvnd : (v2.map sigma.fst).nodup)
            (hal : ∀ (a : Σ a, β a), a ∈ v2 → mk_idx n (hash_fn a.1) = bidx)
            (djuv : (u.map sigma.fst).disjoint (v2.map sigma.fst))
            (djwv : (w.map sigma.fst).disjoint (v2.map sigma.fst))
  include hvnd hal djuv djwv

  theorem valid.modify_aux2 : Π (i) (h : i ≤ n.1) (hb : i > bidx.1) {sz : ℕ},
    valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.iterate_aux bkts (λ_ v l, v :: l) i h []) sz → sz + v2.length ≥ v1.length ∧
    valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.iterate_aux bkts' (λ_ v l, v :: l) i h []) (sz + v2.length - v1.length)
  | 0     _ hb sz := absurd hb (nat.not_lt_zero _)
  | (i+1) h hb sz :=
    match nat.lt_or_eq_of_le $ nat.le_of_succ_le_succ hb with
    | or.inl hl :=
      have bn : bidx ≠ ⟨i, h⟩, from λhh, ne_of_gt hl $ fin.veq_of_eq $ eq.symm hh,
      have he : array.read bkts ⟨i, h⟩ = array.read bkts' ⟨i, h⟩, from
       (show _ = ite (bidx = ⟨i, h⟩) (f _) _, by rw if_neg bn),
      by simp[array.iterate_aux]; rw [← he]; exact λvv,
      let ⟨s, v, nd, al, e⟩ := _root_.hash_map.valid_aux.unfold_cons vv in
      let ⟨hsz, v'⟩ := valid.modify_aux2 i (le_of_lt h) hl v in
      by rw [e, calc (s + (array.read bkts ⟨i, h⟩).length) + v2.length - v1.length
                    = s + v2.length + (array.read bkts ⟨i, h⟩).length - v1.length : by simp
                ... = s + v2.length - v1.length + (array.read bkts ⟨i, h⟩).length : nat.sub_add_comm hsz]; exact
      ⟨nat.le_trans hsz $ nat.add_le_add_right (nat.le_add_right _ _) _,
       valid_aux.cons _ v' nd (by rw bkts'.rev_list_length_aux; rwa bkts.rev_list_length_aux at al)⟩
    | or.inr e :=
      match i, e, h with ._, rfl, h :=
        have array.read bkts' bidx = f L, from
          show ite (bidx = bidx) _ _ = _, by rw if_pos rfl,
        begin
          simp[array.iterate_aux, -add_comm],
          rw [← show bidx = ⟨bidx.1, h⟩, from fin.eq_of_veq rfl,
              ← valid.modify_aux1 _ _ (le_refl _),
              this, hfl, hl],
          exact λvv,
          let ⟨s, v, nd, al, e⟩ := _root_.hash_map.valid_aux.unfold_cons vv in
          have nd' : ((u ++ v2 ++ w).map sigma.fst).nodup, begin
            rw [list.map_append, list.map_append] at nd,
            rw [list.map_append, list.map_append],
            have ndu : (u.map sigma.fst).nodup := list.nodup_of_nodup_append_left (list.nodup_of_nodup_append_left nd),
            have ndv1 : (v1.map sigma.fst).nodup := list.nodup_of_nodup_append_right (list.nodup_of_nodup_append_left nd),
            have ndw : (w.map sigma.fst).nodup := list.nodup_of_nodup_append_right nd,
            have djuw : (u.map sigma.fst).disjoint (w.map sigma.fst) :=
              list.disjoint_of_disjoint_append_left_left (list.disjoint_of_nodup_append nd),
            exact list.nodup_append_of_nodup_of_nodup_of_disjoint
              (list.nodup_append_of_nodup_of_nodup_of_disjoint ndu hvnd djuv)
              ndw (list.disjoint_append_of_disjoint_left djuw djwv.comm)
          end,
          begin
            rw [e, calc s + (u ++ v1 ++ w).length + v2.length - v1.length
                      = s + u.length + v1.length + w.length + v2.length - v1.length : by simp[list.length_append]
                  ... = s + u.length + v2.length + w.length + v1.length - v1.length : by simp
                  ... = s + u.length + v2.length + w.length : by rw[nat.add_sub_cancel]
                  ... = s + (u ++ v2 ++ w).length : by simp[list.length_append, list.length_append]],
            constructor,
            exact calc v1.length
                     ≤ v1.length + (s + u.length + w.length + v2.length) : nat.le_add_right _ _
                 ... = s + (u.length + v1.length + w.length) + v2.length : by simp
                 ... = s + (u ++ v1 ++ w).length + v2.length : by rw[list.length_append, list.length_append],
            apply valid_aux.cons _ v nd',
            intros a muvw,
            simp at al,
            simp at muvw,
            cases muvw with mu mvw,
            exact al a (or.inl mu),
            cases mvw with mv mw,
            rw bkts.rev_list_length_aux,
            exact congr_arg fin.val (hal a mv),
            exact al a (or.inr (or.inr mw)),
          end
        end
      end
    end

  theorem valid.modify {sz : ℕ} : valid bkts sz → sz + v2.length ≥ v1.length ∧ valid bkts' (sz + v2.length - v1.length) :=
  valid.modify_aux2 hl hfl hvnd hal djuv djwv _ _ bidx.2
end

theorem valid.replace_aux (a : α) (b : β a) : Π (l : list (Σ a, β a)), a ∈ l.map sigma.fst →
  ∃ (u w : list Σ a, β a) b', l = u ++ [⟨a, b'⟩] ++ w ∧ replace_aux a b l = u ++ [⟨a, b⟩] ++ w ∧ a ∉ u.map sigma.fst
| []           Hc := false.elim Hc
| (⟨a', b'⟩::t) Hc := begin
  simp at Hc,
  simp [replace_aux, -and.comm],
  exact match (by apply_instance : decidable (a' = a)) with
  | is_true e := match a', b', e with ._, b', rfl := ⟨[], t, b', rfl, rfl, by simp⟩ end
  | is_false ne :=
    let ⟨u, w, b'', hl, hfl, nin⟩ := valid.replace_aux t (or.resolve_left Hc (λe, ne (eq.symm e))) in
    show ∃ (u w : list (Σ (a : α), β a)) (b'_1 : β a), sigma.mk a' b' :: t = u ++ ⟨a, b'_1⟩ :: w ∧
      (sigma.mk a' b' :: hash_map.replace_aux a b t) = u ++ ⟨a, b⟩ :: w ∧ a ∉ list.map sigma.fst u, from
    ⟨⟨a', b'⟩ :: u, w, b'', by simp[hl], by simp[hfl], λm, by {simp at m, cases m with e m, exact ne (eq.symm e), exact nin m}⟩
  end
end

theorem valid.replace {n : ℕ+}
  {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a)
  (Hc : contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (bkts.modify hash_fn a (replace_aux a b)) sz :=
let nd := v.nodup hash_fn (mk_idx n (hash_fn a)) in
let ⟨u, w, b', hl, hfl, nin⟩ := valid.replace_aux a b
  (array.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff _ _ nd).1 Hc) in
and.right $ valid.modify
  u [⟨a, b'⟩] [⟨a, b⟩] w hl hfl (list.nodup_singleton _)
  (λa' e, by simp at e; rw e)
  (λa' e1 e2, by simp at e2; rw e2 at e1; exact nin e1)
  (λa' e1 e2, begin
    simp at e2,
    rw e2 at e1,
    rw [hl, list.map_append, list.map_append] at nd,
    apply list.disjoint_of_nodup_append nd _ e1,
    simp
  end) v

theorem valid.insert {n : ℕ+}
  {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a)
  (Hnc : ¬ contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (reinsert_aux bkts a b) (sz+1) :=
let nd := v.nodup hash_fn (mk_idx n (hash_fn a)) in
and.right $ valid.modify
  [] [] [⟨a, b⟩] (bkts.read hash_fn a) rfl rfl (list.nodup_singleton _)
  (λa' e, by simp at e; rw e)
  (λa', false.elim)
  (λa' e1 e2, begin
    simp at e2,
    rw e2 at e1,
    exact Hnc ((contains_aux_iff _ _ nd).2 e1)
  end) v

theorem valid.erase_aux (a : α) : Π (l : list (Σ a, β a)), a ∈ l.map sigma.fst →
  ∃ (u w : list Σ a, β a) b, l = u ++ [⟨a, b⟩] ++ w ∧ erase_aux a l = u ++ [] ++ w
| []           Hc := false.elim Hc
| (⟨a', b'⟩::t) Hc := begin
  simp at Hc,
  simp [erase_aux],
  exact match (by apply_instance : decidable (a' = a)) with
  | is_true e := match a', b', e with ._, b', rfl := ⟨[], t, b', rfl, rfl⟩ end
  | is_false ne :=
    let ⟨u, w, b'', hl, hfl⟩ := valid.erase_aux t (or.resolve_left Hc (λe, ne (eq.symm e))) in
    ⟨⟨a', b'⟩::u, w, b'', by simp[hl], by simp[ne, hfl]⟩
  end
end

theorem valid.erase {n} {bkts : bucket_array α β n} {sz}
  (a : α) (Hc : contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (bkts.modify hash_fn a (erase_aux a)) (sz-1) :=
let nd := v.nodup _ (mk_idx n (hash_fn a)) in
let ⟨u, w, b, hl, hfl⟩ := valid.erase_aux a (array.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff _ _ nd).1 Hc) in
and.right $ valid.modify
  u [⟨a, b⟩] [] w hl hfl list.nodup.ndnil
  (λa', false.elim) (λa' e1, false.elim) (λa' e1, false.elim) v

end
end hash_map

structure hash_map (α : Type u) [decidable_eq α] (β : α → Type v) :=
(hash_fn : α → nat)
(size : ℕ)
(nbuckets : ℕ+)
(buckets : bucket_array α β nbuckets)
(is_valid : hash_map.valid hash_fn buckets size)

def mk_hash_map {α : Type u} [decidable_eq α] {β : α → Type v} (hash_fn : α → nat) (nbuckets := 8) : hash_map α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
let nz : n > 0 := by abstract { cases nbuckets, {simp, tactic.comp_val}, simp [if_pos, nat.succ_ne_zero], apply nat.zero_lt_succ} in
{ hash_fn  := hash_fn,
  size     := 0,
  nbuckets := ⟨n, nz⟩,
  buckets  := mk_array n [],
  is_valid := hash_map.valid.mk _ _ }

namespace hash_map
variables {α : Type u} {β : α → Type v} [decidable_eq α]

def find (m : hash_map α β) (a : α) : option (β a) :=
find_aux a (m.buckets.read m.hash_fn a)

def contains (m : hash_map α β) (a : α) : bool :=
(m.find a).is_some

instance : has_mem α (hash_map α β) := ⟨λa m, m.contains a⟩

def fold {δ : Type w} (m : hash_map α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
m.buckets.foldl d f

def entries (m : hash_map α β) : list Σ a, β a :=
m.buckets.as_list

def keys (m : hash_map α β) : list α :=
m.entries.map sigma.fst

theorem find_iff (m : hash_map α β) (a : α) (b : β a) :
  m.find a = some b ↔ sigma.mk a b ∈ m.entries :=
m.is_valid.find_aux_iff _ _ _

theorem contains_iff (m : hash_map α β) (a : α) :
  m.contains a ↔ a ∈ m.keys :=
m.is_valid.contains_aux_iff _ _

theorem entries_empty (hash_fn : α → nat) (n) :
  (@mk_hash_map α _ β hash_fn n).entries = [] :=
by dsimp [entries, mk_hash_map]; rw mk_as_list hash_fn

theorem keys_empty (hash_fn : α → nat) (n) :
  (@mk_hash_map α _ β hash_fn n).keys = [] :=
by dsimp [keys]; rw entries_empty; refl

theorem find_empty (hash_fn : α → nat) (n a) :
  (@mk_hash_map α _ β hash_fn n).find a = none :=
by ginduction (@mk_hash_map α _ β hash_fn n).find a with h; [refl,
   { have := (find_iff _ _ _).1 h, rw entries_empty at this, contradiction }]

theorem not_contains_empty (hash_fn : α → nat) (n a) :
  ¬ (@mk_hash_map α _ β hash_fn n).contains a :=
by apply bool_iff_false.2; dsimp [contains]; rw [find_empty]; refl

lemma insert_lemma (hash_fn : α → nat) {n n'}
  {bkts : bucket_array α β n} {sz} (v : valid hash_fn bkts sz) :
  valid hash_fn (bkts.foldl (mk_array _ [] : bucket_array α β n') (reinsert_aux hash_fn)) sz :=
suffices ∀ (l : list Σ a, β a),
  ∀ (t : bucket_array α β n') sz, valid hash_fn t sz → ((l ++ t.as_list).map sigma.fst).nodup →
    valid hash_fn (l.foldl (λr (a : Σ a, β a), reinsert_aux hash_fn r a.1 a.2) t) (sz + l.length),
begin
  have p := this bkts.as_list _ _ (valid.mk _ _),
  rw [mk_as_list hash_fn, list.append_nil, zero_add, v.as_list_length _] at p,
  rw bucket_array.foldl_eq,
  exact p (v.as_list_nodup _),
end,
λl, begin
  induction l with c l IH,
  exact λ t sz v nd, v,
  intros t sz v nd,
  rw (show sz + (c :: l).length = sz + 1 + l.length, by simp),
  simp at nd,
  have nc := list.not_mem_of_nodup_cons nd,
  have v' := v.insert _ _ c.2
    (λHc, nc $ list.mem_append_right _ $
      (v.contains_aux_iff _ c.1).1 Hc),
  apply IH _ _ v',
  simp,
  have nd' := list.nodup_of_nodup_cons nd,
  apply list.nodup_append_of_nodup_of_nodup_of_disjoint
    (list.nodup_of_nodup_append_left nd')
    (v'.as_list_nodup _),
  exact λa m1 m2,
  let ⟨⟨a', b⟩, m1, e1⟩ := list.exists_of_mem_map m1 in
  let ⟨⟨a'', b'⟩, m2, e2⟩ := list.exists_of_mem_map m2 in
  match a', a'', b, b', m1, m2, e1, e2 with ._, ._, b, b', m1, m2, rfl, rfl :=
    let ⟨i, im⟩ := ((reinsert_aux hash_fn t c.1 c.2).mem_as_list _).1 m2 in
    have im : sigma.mk a b' ∈ ite _ _ _, from im,
    have sigma.mk a b' ∉ array.read t i, from λm3,
      have a ∈ list.map sigma.fst (bucket_array.as_list t), from
      list.mem_map sigma.fst ((t.mem_as_list _).2 ⟨_, m3⟩),
      list.disjoint_of_nodup_append nd' (list.mem_map sigma.fst m1) this,
    if h : mk_idx n' (hash_fn c.1) = i
    then by simp[h] at im; exact or.elim im
      (λe, nc $ list.mem_append_left _ (by rwa [← show a = c.fst, from congr_arg sigma.fst e]))
      this
    else by simp[h] at im; exact this im
  end
end

def insert : Π (m : hash_map α β) (a : α) (b : β a), hash_map α β
| ⟨hash_fn, size, n, buckets, v⟩ a b :=
let bkt := buckets.read hash_fn a in
if hc : contains_aux a bkt then
{ hash_fn  := hash_fn,
  size     := size,
  nbuckets := n,
  buckets  := buckets.modify hash_fn a (replace_aux a b),
  is_valid := v.replace _ a b hc }
else
let size'    := size + 1,
    buckets' := buckets.modify hash_fn a (λl, ⟨a, b⟩::l),
    valid'   := v.insert _ a b hc in
if size' ≤ n.1 then
{ hash_fn  := hash_fn,
  size     := size',
  nbuckets := n,
  buckets  := buckets',
  is_valid := valid' }
else
let n'        : ℕ+ := ⟨n.1 * 2, mul_pos n.2 dec_trivial⟩,
    buckets'' : bucket_array α β n' :=
                buckets'.foldl (mk_array _ []) (reinsert_aux hash_fn) in
{ hash_fn  := hash_fn,
  size     := size',
  nbuckets := n',
  buckets  := buckets'',
  is_valid := insert_lemma _ valid' }

theorem mem_insert : Π (m : hash_map α β) (a b a' b'),
  sigma.mk a' b' ∈ (m.insert a b).entries ↔
  if a = a' then b == b' else sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a b a' b' :=
let bkt  := bkts.read hash_fn a,
    nd : (bkt.map sigma.fst).nodup := v.nodup hash_fn (mk_idx n (hash_fn a)) in
have lem : Π (bkts' : bucket_array α β n) (v1 u w)
  (hl : bucket_array.as_list bkts = u ++ v1 ++ w)
  (hfl : bucket_array.as_list bkts' = u ++ [⟨a, b⟩] ++ w)
  (veq : (v1 = [] ∧ ¬ contains_aux a bkt) ∨ ∃b'', v1 = [⟨a, b''⟩]),
  sigma.mk a' b' ∈ bkts'.as_list ↔
  if a = a' then b == b' else sigma.mk a' b' ∈ bkts.as_list, from
λbkts' v1 u w hl hfl veq, by rw [hl, hfl]; exact
if h : a = a' then by simp[h]; exact
  match a', b', h with ._, b', rfl :=
    have nd' : _, from v.as_list_nodup _,
    have a ∉ u.map sigma.fst ++ w.map sigma.fst, from match v1, veq, hl with
    | ._, or.inl ⟨rfl, Hnc⟩, hl := let na := (not_iff_not_of_iff $ v.contains_aux_iff _ _).1 Hnc in
      have bkts.as_list.map sigma.fst = u.map sigma.fst ++ w.map sigma.fst, by simp [hl],
      by rw this at na; exact na
    | ._, or.inr ⟨b'', rfl⟩, hl := by {
      have nd' := v.as_list_nodup _,
      rw hl at nd', simp at nd',
      exact list.not_mem_of_nodup_cons (list.nodup_head nd') }
    end,
    show sigma.mk a b' = ⟨a, b⟩ ∨ sigma.mk a b' ∈ u ∨ sigma.mk a b' ∈ w ↔ b == b', from
    ⟨λo, match o with
    | or.inl e := by injection e with _ e; exact heq.symm e
    | or.inr (or.inl mu) := absurd (list.mem_append_left _ (list.mem_map sigma.fst mu)) this
    | or.inr (or.inr mw) := absurd (list.mem_append_right _ (list.mem_map sigma.fst mw)) this
    end,
    λe, or.inl $ congr_arg (sigma.mk a) $ eq.symm $ eq_of_heq e⟩
  end
else match v1, veq, hl with
| ._, or.inl ⟨rfl, Hnc⟩, hl := by {
  simp[h],
  refine ⟨λo, or.elim o (λ(hn : sigma.mk a' b' = ⟨a, b⟩), _) id, or.inr⟩,
  { injection hn with hn _, exact absurd hn.symm h } }
| ._, or.inr ⟨b'', rfl⟩, hl := by {
  simp[h],
  refine or_congr ⟨λ(hn : sigma.mk a' b' = ⟨a, b⟩), _,
                   λ(hn : sigma.mk a' b' = ⟨a, b''⟩), _⟩ (iff.refl _);
  { injection hn with hn _, exact absurd hn.symm h } }
end,
by simp[insert]; exact
match (by apply_instance : decidable (contains_aux a bkt)) with
| is_true Hc :=
  let bkts' := bkts.modify hash_fn a (replace_aux a b),
      ⟨u', w', b'', hl', hfl', _⟩ := valid.replace_aux a b
        (array.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff _ _ nd).1 Hc),
      ⟨u, w, hl, hfl⟩ := show ∃ u' w', _ ∧ bkts'.as_list = _, from
        append_of_modify u' [⟨a, b''⟩] [⟨a, b⟩] w' hl' hfl' in
  lem bkts' _ u w hl hfl $ or.inr ⟨b'', rfl⟩
| is_false Hnc :=
  let size'    := size + 1,
      bkts' := bkts.modify hash_fn a (λl, ⟨a, b⟩::l) in
  have sigma.mk a' b' ∈ bkts'.as_list ↔ if a = a' then b == b' else sigma.mk a' b' ∈ bkts.as_list, from
  let ⟨u, w, hl, hfl⟩ := show ∃ u' w', _ ∧ bkts'.as_list = _, from
        append_of_modify [] [] [⟨a, b⟩] _ rfl rfl in
  lem bkts' _ u w hl hfl $ or.inl ⟨rfl, Hnc⟩,
  match (by apply_instance : decidable (size' ≤ n.1)) with
  | is_true _ := this
  | is_false _ :=
    let n' : ℕ+ := ⟨n.1 * 2, mul_pos n.2 dec_trivial⟩,
        bkts'' : bucket_array α β n' := bkts'.foldl (mk_array _ []) (reinsert_aux hash_fn) in
    suffices h : sigma.mk a' b' ∈ bkts''.as_list ↔ sigma.mk a' b' ∈ bkts'.as_list.reverse,
      from h.trans $ (list.mem_reverse _ _).trans this,
    have h : bkts'' = bkts'.as_list.foldl _ _, from bkts'.foldl_eq _ _,
    begin
      rw [← list.foldr_reverse] at h, rw h,
      induction bkts'.as_list.reverse with a l IH,
      { simp, rw[mk_as_list hash_fn n'], simp },
      { cases a with a'' b'', simp, rw [← IH], exact
        let B := l.foldr (λ y (x : bucket_array α β n'),
              reinsert_aux hash_fn x y.1 y.2) (mk_array n'.1 []),
            ⟨u, w, hl, hfl⟩ := show ∃ u' w', B.as_list = _ ∧
              (reinsert_aux hash_fn B a'' b'').as_list = _, from
          append_of_modify [] [] [⟨a'', b''⟩] _ rfl rfl in
        by simp [hl, hfl] }
    end
  end
end

theorem find_insert_eq (m : hash_map α β) (a : α) (b : β a) : (m.insert a b).find a = some b :=
(find_iff (m.insert a b) a b).2 $ (mem_insert m a b a b).2 $ by rw if_pos rfl

theorem find_insert_ne (m : hash_map α β) (a a' : α) (b : β a) (h : a ≠ a') :
  (m.insert a b).find a' = m.find a' :=
option.eq_of_eq_some $ λb',
let t := mem_insert m a b a' b' in
(find_iff _ _ _).trans $ iff.trans (by rwa if_neg h at t) (find_iff _ _ _).symm

theorem find_insert (m : hash_map α β) (a' a : α) (b : β a) :
  (m.insert a b).find a' = if h : a = a' then some (eq.rec_on h b) else m.find a' :=
if h : a = a' then by rw dif_pos h; exact
  match a', h with ._, rfl := find_insert_eq m a b end
else by rw dif_neg h; exact find_insert_ne m a a' b h

def insert_all (l : list (Σ a, β a)) (m : hash_map α β) : hash_map α β :=
l.foldl (λ m ⟨a, b⟩, insert m a b) m

def of_list (l : list (Σ a, β a)) (hash_fn): hash_map α β :=
insert_all l (mk_hash_map hash_fn (2 * l.length))

def erase (m : hash_map α β) (a : α) : hash_map α β :=
match m with ⟨hash_fn, size, n, buckets, v⟩ :=
  if hc : contains_aux a (buckets.read hash_fn a) then
  { hash_fn  := hash_fn,
    size     := size - 1,
    nbuckets := n,
    buckets  := buckets.modify hash_fn a (erase_aux a),
    is_valid := v.erase _ a hc }
  else m
end

theorem mem_erase : Π (m : hash_map α β) (a a' b'),
  sigma.mk a' b' ∈ (m.erase a).entries ↔
  a ≠ a' ∧ sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a a' b' :=
let bkt := bkts.read hash_fn a in
by simp[erase]; exact
match (by apply_instance : decidable (contains_aux a bkt)) with
| is_true Hc :=
  let bkts' := bkts.modify hash_fn a (erase_aux a) in
  show sigma.mk a' b' ∈ bkts'.as_list ↔ a ≠ a' ∧ sigma.mk a' b' ∈ bkts.as_list, from
  let nd := v.nodup _ (mk_idx n (hash_fn a)) in
  let ⟨u', w', b, hl', hfl'⟩ := valid.erase_aux a bkt ((contains_aux_iff _ _ nd).1 Hc) in
  match bkts.as_list, bkts'.as_list,
        append_of_modify u' [⟨a, b⟩] [] _ hl' hfl', v.as_list_nodup _ with
  | ._, ._, ⟨u, w, rfl, rfl⟩, nd' := by simp; simp at nd'; exact
    ⟨λhm, ⟨λe, match a', e, b', hm with ._, rfl, b', hm := by {
      rw [← list.mem_append_iff] at hm;
      have hm := list.mem_map sigma.fst hm;
      rw list.map_append at hm;
      exact list.not_mem_of_nodup_cons (list.nodup_head nd') hm }
    end, or.inr hm⟩,
    λ⟨hn, o⟩, or.elim o (λhm, by injection hm with hm; exact absurd hm.symm hn) id⟩
  end
| is_false Hnc :=
  by refine ⟨λ(h : sigma.mk a' b' ∈ bkts.as_list), ⟨_, h⟩, and.right⟩;
  exact λe, match a', e, b', h with ._, rfl, b, h :=
    Hnc $ (v.contains_aux_iff _ _).2 (list.mem_map sigma.fst h)
  end
end

theorem find_erase_eq (m : hash_map α β) (a : α) : (m.erase a).find a = none :=
begin
  ginduction (m.erase a).find a with h b, refl,
  exact absurd rfl ((mem_erase m a a b).1 ((find_iff (m.erase a) a b).1 h)).left
end

theorem find_erase_ne (m : hash_map α β) (a a' : α) (h : a ≠ a') :
  (m.erase a).find a' = m.find a' :=
option.eq_of_eq_some $ λb',
(find_iff _ _ _).trans $ (mem_erase m a a' b').trans $
  (and_iff_right h).trans (find_iff _ _ _).symm

theorem find_erase (m : hash_map α β) (a' a : α) :
  (m.erase a).find a' = if a = a' then none else m.find a' :=
if h : a = a' then by rw if_pos h; exact
  match a', h with ._, rfl := find_erase_eq m a end
else by rw if_neg h; exact find_erase_ne m a a' h

section string
variables [has_to_string α] [∀ a, has_to_string (β a)]
open prod
private def key_data_to_string (a : α) (b : β a) (first : bool) : string :=
(if first then "" else ", ") ++ sformat!"{a} ← {b}"

private def to_string (m : hash_map α β) : string :=
"⟨" ++ (fst (fold m ("", tt) (λ p a b, (fst p ++ key_data_to_string a b (snd p), ff)))) ++ "⟩"

instance : has_to_string (hash_map α β) :=
⟨to_string⟩

end string

section format
open format prod
variables [has_to_format α] [∀ a, has_to_format (β a)]

private meta def format_key_data (a : α) (b : β a) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

private meta def to_format (m : hash_map α β) : format :=
group $ to_fmt "⟨" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ p a b, (fst p ++ format_key_data a b (snd p), ff)))) ++
        to_fmt "⟩"

meta instance : has_to_format (hash_map α β) :=
⟨to_format⟩
end format
end hash_map

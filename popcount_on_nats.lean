open BitVec

/-! Prototype proof: recursive addition on a list of `Nat` is equivalent to PPS on the same list -/

/--
  We define addition on a list of naturals `l` recursively. If the queried index is out of bounds, we add `0`.
-/
def recursive_addition_list (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | head :: tail => head + recursive_addition_list tail

theorem cons_recursive_addition_list (newEl : Nat) (l : List Nat) :
  recursive_addition_list (newEl :: l) = newEl + recursive_addition_list l := by rfl

theorem List.exists_concat_of_length_eq_add_one {l : List α} : l.length = n + 1 → ∃ h t, l = t ++ [h] := by
  intros hl
  exists l.getLast (by exact List.ne_nil_of_length_eq_add_one hl)
  exists l.dropLast
  exact Eq.symm (List.dropLast_concat_getLast (List.ne_nil_of_length_eq_add_one hl))

theorem concat_recursive_addition_list (newEl : Nat) (l : List Nat) :
    recursive_addition_list (l ++ [newEl]) = newEl + recursive_addition_list l := by
  induction l
  · unfold recursive_addition_list
    unfold recursive_addition_list
    simp
  · case _ head tail ih =>
    unfold recursive_addition_list
    simp
    rw [ih,
      show head + (newEl + recursive_addition_list tail) = newEl + (head + recursive_addition_list tail) by omega]

theorem concat_eq_of_le_two (l : List Nat) (hl : 2 ≤ l.length):
  ∃ (e1 e2 : Nat), ∃ (tail : List Nat),
    l = tail ++ [e1] ++ [e2] := by
  obtain ⟨h, t, hnl⟩ := List.exists_concat_of_length_eq_add_one (l := l) (n := l.length - 1) (by omega)
  have : t.length = l.length - 1 := by simp [hnl]
  obtain ⟨h', t', hnl'⟩ := List.exists_concat_of_length_eq_add_one (l := t) (n := l.length - 2) (by omega)
  rw [hnl'] at hnl
  exists h', h, t'

def rec_add_eq_rec_add_iff (a b : List Nat) (n : Nat)
    (hlen : a.length = (b.length + 1) / 2)
    (hn : n = a.length)
    (hadd : ∀ i (hi : i < a.length) (hi' : 2 * i < b.length),
        a[i] = b[2 * i] + (if h : 2 * i + 1 < b.length then b[2 * i + 1] else 0)) :
      recursive_addition_list a = recursive_addition_list b := by
    induction n generalizing a b
    · have hblen : b.length = 0 := by omega
      have hb := (List.length_eq_zero_iff (l := b)).mp hblen
      have ha := (List.length_eq_zero_iff (l := a)).mp (by omega)
      simp [ha, hb]
    · case _ n ihn =>
      obtain ⟨ha', taila, htaila⟩:= List.exists_concat_of_length_eq_add_one (l := a) (n := n) (by omega)
      rw [htaila, concat_recursive_addition_list]
      have hahead : ha' = a[n] := by
        simp [htaila]
        rw [List.getElem_concat_length (by simp [htaila] at hn; exact hn)]
      rw [hahead]
      rw [hadd (i := n) (by omega) (by omega)]
      split
      · case _ ht =>
        have hblenle: 2 ≤ b.length := by omega
        obtain ⟨e1, e2, tailb, htailb⟩ := concat_eq_of_le_two (l := b) (by omega)
        conv =>
          rhs
          rw [htailb]
          rw [concat_recursive_addition_list]
          rw [concat_recursive_addition_list]
        have hblen : b.length = tailb.length + 2 := by
          subst htailb; simp
        have halen : a.length = taila.length + 1 := by
          subst htaila; simp
        have he1 : b[2 * n] = e1 := by
          simp [htailb]
          rw [List.getElem_append]
          have : 2 * n = tailb.length := by omega
          simp [show ¬ 2 * n < tailb.length by omega, show 2 * n - tailb.length = 0 by omega]
        have he2 : b[2 * n + 1] = e2 := by
          simp [htailb]
          rw [List.getElem_append]
          have : 2 * n = tailb.length := by omega
          simp [show ¬ 2 * n + 1 < tailb.length by omega, show 2 * n + 1 - tailb.length = 1 by omega]
        rw [he1, he2,
            show e2 + (e1 + recursive_addition_list tailb) = e1 + e2 + recursive_addition_list tailb by omega]
        simp only [Nat.add_left_cancel_iff]
        apply ihn
        · omega
        · omega
        · intros j hj hj'
          specialize hadd j (by omega) (by omega)
          have ho : 2 * j + 1 < tailb.length := by omega
          have ho' : 2 * j < tailb.length + 1 := by omega
          simp only [htaila, hj, List.getElem_append_left, htailb, List.append_assoc,
            List.cons_append, List.nil_append, hj', List.length_append, List.length_cons,
            List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_lt_add_iff_right,
            ho', reduceDIte,
            ho] at hadd
          simp [ho, hadd]
      · case _ hf =>
        have : 1 ≤ b.length := by omega
        obtain ⟨hb', tailb, htailb⟩:= List.exists_concat_of_length_eq_add_one (l := b) (n := 2 * n) (by omega)
        conv =>
          rhs
          rw [htailb]
          rw [concat_recursive_addition_list]
        have hblen : b.length = tailb.length + 1 := by
          subst htailb; simp
        have halen : a.length = taila.length + 1 := by
          subst htaila; simp
        have heq : b[2 * n] = hb' := by
          simp only [htailb, List.getElem_append]
          have : 2 * n = tailb.length := by omega
          simp [show ¬ 2 * n < tailb.length by omega, show 2 * n - tailb.length = 0 by omega]
        rw [heq]
        simp
        apply ihn
        · omega
        · omega
        · intros j hj hj'
          specialize hadd j (by omega) (by omega)
          have ho : 2 * j + 1 < tailb.length := by omega
          have ho' : 2 * j < tailb.length + 1 := by omega
          simp only [htaila, hj, List.getElem_append_left, htailb, hj', List.length_append,
            List.length_cons, List.length_nil, Nat.zero_add, Nat.add_lt_add_iff_right, ↓reduceDIte,
            ho] at hadd
          simp only [hadd, Nat.add_left_cancel_iff]
          split <;> rfl

/--
  We define the addition of a new element in the parallel-prefix-sum tree as addition of two adjacent elements
  in the previous layer of the tree.
  We require preserving the `proof_addition` that, at every iteration, each element in `new_layer` results from
  the addition of two adjacent elements in `old_layer`, and preserve the proof in the result as well.
  We also preserve the `proof_length` that the lenght of `new_layer` is at most `(old_layer.length + 1)/2`.
  Showing that the length of `new_layer` decreases is necessary to show termination in the construction of the tree.
  Finally, we preserve the proof that the length of `new_layer` increases by at most `1` at every iteration
-/
def pps_new_element_in_layer (old_layer : List Nat) (new_layer : List Nat) (iter_num : Nat)
  (hnew : new_layer.length = iter_num)
  (hold : 2 * (iter_num - 1) < old_layer.length)
  (proof_addition : ∀ i (h: i < new_layer.length) (h' : 2 * i < old_layer.length),
        new_layer[i] = old_layer[2 * i] + (if h : 2 * i + 1< old_layer.length then old_layer[2 * i + 1] else 0))
  :
    {ls : List Nat //
      (∀ i (h: i < ls.length) (h' : 2 * i < old_layer.length),
        ls[i] = old_layer[2 * i] + (if h : 2 * i + 1< old_layer.length then old_layer[2 * i + 1] else 0)) ∧ (ls.length = (old_layer.length + 1)/2)
    } :=
  match hlen : old_layer.length - (iter_num * 2) with
  | 0 =>
    ⟨new_layer, by
      and_intros
      · exact proof_addition
      · by_cases h0 : iter_num = 0
        · simp_all
        · omega
    ⟩
  | n + 1 =>
        let op1 := old_layer[2 * iter_num]
        let op2 := if hlt : (2 * iter_num + 1) < old_layer.length then old_layer[2 * iter_num + 1] else 0
        let new_layer' := new_layer.append [op1 + op2]
        have proof_new_layer_length_eq_iter :
              new_layer'.length = iter_num + 1 := by simp [new_layer']; omega
        have proof_old_layer_length_lt : 2 * (iter_num + 1 - 1) < old_layer.length := by omega
        have proof_new_layer_elements_eq_old_layer_add :
              ∀ (i : Nat) (h : i < new_layer'.length) (h' : 2 * i < old_layer.length),
                new_layer'[i] = old_layer[2 * i] + if h : 2 * i + 1 < old_layer.length then old_layer[2 * i + 1] else 0 := by
            intros i hi hi'
            by_cases hi'' : i < new_layer.length
            · -- for the elements already in `new_layer` the proof already exists in `proof_addition`
              simp only [List.append_eq, hi'', List.getElem_append_left, new_layer']
              exact proof_addition i (by omega) (by omega)
            · -- otherwise, the proof is given by the construction of the newly-appended element
              simp only [List.append_eq, List.getElem_append, show ¬i < new_layer.length by omega,
                reduceDIte, List.getElem_singleton, new_layer', op1, op2]
              simp only [show i = iter_num by omega]
        pps_new_element_in_layer old_layer new_layer' (iter_num + 1)
                proof_new_layer_length_eq_iter
                proof_old_layer_length_lt
                proof_new_layer_elements_eq_old_layer_add
termination_by old_layer.length - (iter_num * 2)

/--
  We construct the parallel-prefix-sum tree.
  Given a list `l`, we construct a new layer and obtain two proofs:
  · `proof_new_layer`, ensuring that the new layer contains the sum of the previous layer
  · `proof_length_new_layer`, ensuring that the new layer's length decreases (and therefore recursion terminates)
  In this definition, we preserve the `proof` that the recursive addition at any produced layers remains constant.
-/
def parallel_prefix_sum_list (l : List Nat) (k : Nat)
      (proof : recursive_addition_list l = k)
      (proof_length : 0 < l.length) :
    {ls : List Nat // recursive_addition_list ls = k ∧ ls.length = 1} :=
  if h : l.length = 1 then
    ⟨l, by
          and_intros
          · exact proof
          · omega⟩
  else
    let ⟨new_layer, proof_new_layer, proof_length_new_layer⟩ := pps_new_element_in_layer l [] 0 (by simp) (by simp; omega) (by simp)
    let proof_sum_eq : recursive_addition_list new_layer = k := by
      -- every element of `new_layer` results from the sum of two adjacent elements in `l` (by `proof_new_layer`)
      -- we proceed by induction on the length of the list recursively summated
      rw [← proof]
      apply rec_add_eq_rec_add_iff (a := new_layer) (b := l) (n := new_layer.length) (by omega) (by omega)
      exact proof_new_layer
    let proof_new_layer_length : 0 < new_layer.length := by omega
    parallel_prefix_sum_list new_layer k proof_sum_eq proof_new_layer_length

/--
  We prove that the recursive sum on a list and the summation via parallel prefix sum are equivalenet.
-/
theorem pps_eq_rec_of_lt (l : List Nat) (hl : 0 < l.length) :
    parallel_prefix_sum_list l (recursive_addition_list l) (by rfl) hl = [recursive_addition_list l] := by
  have ⟨pps_val, pps_proof_addition, pps_proof_length⟩ :=
        parallel_prefix_sum_list l (recursive_addition_list l) (by rfl) hl
  simp only [← pps_proof_addition]
  unfold recursive_addition_list
  unfold recursive_addition_list
  obtain ⟨el, rfl⟩ := (List.length_eq_one_iff (l := pps_val)).mp pps_proof_length
  simp

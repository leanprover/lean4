/- We use the following auxiliary type instead of (Σ α : Type, α)
   because the code generator produces better code for `pointed`.
   For `pointed`, the code generator erases the field `α`. -/
structure pointed :=
(α : Type) (a : α)

/- The following two commands demonstrate the difference.
   To remove the overhead in the `sigma` case, the code
   generator would have to support code specialization. -/
#eval pointed.mk nat 10
#eval (⟨nat, 10⟩ : Σ α : Type, α)

structure heap :=
(size : nat)
(mem  : array size pointed)

structure ref (α : Type) :=
(idx : nat)

def in_heap {α : Type} (r : ref α) (h : heap) : Prop :=
∃ hlt : r.idx < h.size, (h.mem.read ⟨r.idx, hlt⟩).1 = α

lemma lt_of_in_heap {α : Type} {r : ref α} {h : heap} (hin : in_heap r h) : r.idx < h.size :=
by cases hin; assumption

lemma cast_of_in_heap {α : Type} {r : ref α} {h : heap} (hin : in_heap r h) : (h.mem.read ⟨r.idx, lt_of_in_heap hin⟩).1 = α :=
by cases hin; exact hin_h

def mk_ref : heap → Π {α : Type}, α → ref α × heap
| ⟨n, mem⟩ α v := ({idx := n}, { size := n+1, mem := mem.push_back ⟨α, v⟩ })

def read : Π (h : heap) {α : Type} (r : ref α) (prf : in_heap r h), α
| ⟨n, mem⟩ α r hin := eq.rec_on (cast_of_in_heap hin) (mem.read ⟨r.idx, lt_of_in_heap hin⟩).2

def write : Π (h : heap) {α : Type} (r : ref α) (prf : in_heap r h) (a : α), heap
| ⟨n, mem⟩ α r hin a := { size := n, mem := mem.write ⟨r.idx, lt_of_in_heap hin⟩ ⟨α, a⟩ }

lemma in_heap_mk_ref (h : heap) {α : Type} (a : α) : in_heap (mk_ref h a).1 (mk_ref h a).2 :=
begin
 cases h, simp [mk_ref, in_heap], dsimp,
 have : h_size < h_size + 1, { apply nat.lt_succ_self },
 existsi this,
 simp [array.push_back, array.read, d_array.read, *]
end

lemma in_heap_mk_ref_of_in_heap {α β : Type} {h : heap} {r : ref α} (b : β) : in_heap r h → in_heap r (mk_ref h b).2 :=
begin
  intro hin,
  have := lt_of_in_heap hin,
  have hlt := nat.lt_succ_of_lt this,
  cases h, simp [in_heap, mk_ref, *] at *, dsimp,
  have : r.idx ≠ h_size, { intro heq, subst heq, exact absurd this (irrefl _) },
  simp [array.push_back, array.read, d_array.read, *],
  existsi hlt, cases hin, assumption
end

@[simp] lemma fin.mk_eq {n : nat} {i j : nat} (h₁ : i < n) (h₂ : j < n) (h₃ : i ≠ j) : fin.mk i h₁ ≠ fin.mk j h₂ :=
fin.ne_of_vne h₃

lemma in_heap_write_of_in_heap {α β : Type} {h : heap} {r₁ : ref β} {r₂ : ref α} (a : α) : ∀ (hin₁ : in_heap r₁ h) (hin₂ : in_heap r₂ h), in_heap r₁ (write h r₂ hin₂ a) :=
begin
  intros,
  have := lt_of_in_heap hin₁,
  have := lt_of_in_heap hin₂,
  have := cast_of_in_heap hin₁,
  have := cast_of_in_heap hin₂,
  cases h, simp [in_heap, write, *] at *,
  dsimp, existsi this,
  by_cases r₂.idx = r₁.idx,
  { simp [*] at * },
  { simp [*] }
end

inductive is_extension : heap → heap → Prop
| refl      : ∀ h, is_extension h h
| by_mk_ref (h' h : heap) {α : Type} (a : α) (he : is_extension h' h) : is_extension (mk_ref h' a).2 h
| by_write  (h' h : heap) {α : Type} (r : ref α) (hin : in_heap r h') (a : α) (he : is_extension h' h) : is_extension (write h' r hin a) h

lemma is_extension.trans {h₁ h₂ h₃ : heap} : is_extension h₁ h₂ → is_extension h₂ h₃ → is_extension h₁ h₃ :=
begin
 intro he₁, induction he₁,
 { intros, assumption },
 all_goals { intro he₂, constructor, apply he₁_ih, assumption }
end

lemma in_heap_of_is_extension_of_in_heap {α : Type} {r : ref α} {h h' : heap} : is_extension h' h → in_heap r h → in_heap r h' :=
begin
  intro he, induction he generalizing α r,
  { intros, assumption },
  { intro hin, apply in_heap_mk_ref_of_in_heap, apply he_ih, assumption },
  { intro hin, apply in_heap_write_of_in_heap, apply he_ih, assumption }
end

import data.vector namespace Ex
universe u
-- def vector (α : Type u) (n : ℕ) := { l : list α // l.length = n }
namespace vector
variables {α : Type u} {n : ℕ}
@[pattern] def cons : α → vector α n → vector α (nat.succ n)
| a ⟨ v, h ⟩ := ⟨ a::v, congr_arg nat.succ h ⟩

def to_list' (v : vector α n) : list α := v.1

def drop (i : ℕ) : vector α n → vector α (n - i)
| ⟨l, p⟩ := ⟨ list.drop i l, by simp * ⟩

protected axiom eq {n : ℕ} : ∀ (a1 a2 : vector α n), to_list' a1 = to_list' a2 → a1 = a2

@[simp] axiom to_list'_cons (a : α) (v : vector α n) : to_list' (cons a v) = list.cons a (to_list' v)

@[simp] axiom to_list'_drop {n m : ℕ} (v : vector α m) : to_list' (drop n v) = list.drop n (to_list' v)
end vector

open Ex.vector

@[reducible] def bitvec (n : ℕ) := vector bool n

def byte_type := bitvec 8

-- A byte is formed from concatenating two bits and a 6-bit field.
def mk_byte (a b : bool) (l : bitvec 6) : byte_type := cons a (cons b l)

-- Get the third component
def get_data (byte : byte_type) : bitvec 6 := vector.drop 2 byte

lemma get_data_mk_byte {a b : bool} {l : bitvec 6} : get_data (mk_byte a b l) = l :=
begin
  apply vector.eq,
  unfold mk_byte,
  unfold get_data,
  simp
end
end Ex

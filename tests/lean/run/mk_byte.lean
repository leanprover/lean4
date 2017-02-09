import data.bitvec

open vector

def byte_type := bitvec 8

-- A byte is formed from concatenating two bits and a 6-bit field.
def mk_byte (a b : bool) (l : bitvec 6) : byte_type := a :: b :: l

-- Get the third component
def get_data (byte : byte_type) : bitvec 6 := vector.dropn 2 byte

lemma get_data_mk_byte {a b : bool} {l : bitvec 6} : get_data (mk_byte a b l) = l :=
begin
  apply vector.eq,
  unfold mk_byte,
  unfold get_data,
  simp [to_list_dropn, to_list_cons, list.dropn]
end

structure coding :=
(code        : Type)
[code_dec_eq : decidable_eq code]
(decode      : code → Type)

instance coding_code_has_dec_eq (β : coding) : decidable_eq β.code :=
β.code_dec_eq

@[reducible] def typeof (β : coding) (c : β.code) : Type :=
β.decode c

structure ref {code : Type} (c : code) :=
(idx : nat)

structure heap (β : coding) :=
(next : nat)
(mem  : array next (Σ c : β.code, β.decode c))

def mk_heap (β : coding) : heap β :=
{ next := 0, mem := array.nil }

def mk_ref {β : coding} : heap β → Π c : β.code, typeof β c → ref c × heap β
| ⟨n, mem⟩ c v :=
  ({ idx := n }, ⟨n+1, mem.push_back ⟨c, v⟩⟩)

def read {β : coding} {c : β.code} (h : heap β) (r : ref c) : option (typeof β c) :=
match h, r with
| ⟨n, mem⟩, {idx := i} :=
  if h₁ : i < n
  then let ⟨c', v⟩ := mem.read ⟨i, h₁⟩ in
       if h₂ : c' = c
       then eq.rec_on h₂ v
       else none
  else none
end

def write {β : coding} {c : β.code} (h : heap β) (r : ref c) (v : typeof β c) : heap β :=
match h, v with
| ⟨n, mem⟩, v :=
  if h₁ : r.idx < n
  then ⟨n, mem.write ⟨r.idx, h₁⟩ ⟨c, v⟩⟩
  else h
end

@[derive decidable_eq]
inductive simple_code
| Pair : simple_code → simple_code → simple_code
| Bool : simple_code
| Nat  : simple_code
| Ref  : simple_code → simple_code

open simple_code

def decode_simple_code : simple_code → Type
| Bool         := bool
| Nat          := nat
| (Ref c)      := ref c
| (Pair c₁ c₂) := decode_simple_code c₁ × decode_simple_code c₂

def PairRefNat := Pair (Ref Nat) (Ref Nat)

def C : coding :=
{ code := simple_code, decode := decode_simple_code }

def h : heap C :=
let h₀       := mk_heap C in
let (r₀, h₁) := mk_ref h₀ Bool tt in
let (r₁, h₂) := mk_ref h₁ Nat (10:nat) in
let (r₂, h₃) := mk_ref h₂ PairRefNat (r₁, r₁) in
let h₄       := write h₃ r₀ ff in
let h₅       := write h₄ r₁ (20:nat) in
h₅

def r₀ : ref Bool := { idx := 0 }
def r₁ : ref Nat  := { idx := 1 }
def r₂ : ref PairRefNat := { idx := 2 }

#eval @id (option nat) $ read h r₁

/- In the following example the type_context exposes the internal encoding of decode_simple_code.
   TODO(Leo): fix this issue by using refl lemmas. -/
#eval
match read h r₂ : _ → option nat with
| some (r, _) := read h r -- to observe problem, hover over the first `r`
| none        := some 0
end

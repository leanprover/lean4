import Std.Tactic.BVDecide

/-!
Finite-word contracts for the native collector's intrusive links. These proofs describe the
little-endian header layout and bounded addresses required by `set_next` / `get_next`; they do not
verify C++ execution, pointer provenance, the allocator, atomics, or callbacks.
-/

namespace NativeContracts

abbrev Memory := Nat → BitVec 8

/-- The 64-bit branch retains bytes 6 and 7 and inserts an unmasked pointer. -/
def pack64 (header next : BitVec 64) : BitVec 64 :=
  ((header >>> 48) <<< 48) ||| next

def unpack64 (header : BitVec 64) : BitVec 64 := header &&& 0x0000FFFFFFFFFFFF

def Fits64 (next : BitVec 64) : Prop := next >>> 48 = 0

def tag (header : BitVec 64) : BitVec 8 := (header >>> 56).setWidth 8

def other (header : BitVec 64) : BitVec 8 := (header >>> 48).setWidth 8

theorem unpack_pack64 (header next : BitVec 64) (h : Fits64 next) :
    unpack64 (pack64 header next) = next := by
  unfold Fits64 at h
  unfold pack64 unpack64
  bv_decide

theorem pack64_preserves_metadata (header next : BitVec 64) (h : Fits64 next) :
    tag (pack64 header next) = tag header ∧ other (pack64 header next) = other header := by
  unfold Fits64 at h
  unfold tag other pack64
  bv_decide

/-- The 32-bit branch overwrites only the reference-count word, retaining bytes 4 through 7. -/
def pack32 (header : BitVec 64) (next : BitVec 32) : BitVec 64 :=
  (header &&& 0xFFFFFFFF00000000) ||| next.setWidth 64

def unpack32 (header : BitVec 64) : BitVec 32 := header.setWidth 32

theorem unpack_pack32 (header : BitVec 64) (next : BitVec 32) :
    unpack32 (pack32 header next) = next := by
  unfold pack32 unpack32
  bv_decide

theorem pack32_preserves_metadata (header : BitVec 64) (next : BitVec 32) :
    (pack32 header next) >>> 32 = header >>> 32 ∧
    tag (pack32 header next) = tag header ∧ other (pack32 header next) = other header := by
  unfold pack32 tag other
  bv_decide

/-- A byte-addressed store, confined to `count` bytes starting at `base`. -/
def store (mem : Memory) (base count : Nat) (word : BitVec 64) : Memory :=
  fun p => if base ≤ p ∧ p < base + count then (word >>> (8 * (p - base))).setWidth 8 else mem p

def load64 (mem : Memory) (base : Nat) : BitVec 64 :=
  (mem base).setWidth 64 ||| ((mem (base + 1)).setWidth 64 <<< 8) |||
  ((mem (base + 2)).setWidth 64 <<< 16) ||| ((mem (base + 3)).setWidth 64 <<< 24) |||
  ((mem (base + 4)).setWidth 64 <<< 32) ||| ((mem (base + 5)).setWidth 64 <<< 40) |||
  ((mem (base + 6)).setWidth 64 <<< 48) ||| ((mem (base + 7)).setWidth 64 <<< 56)

theorem load_store64 (mem : Memory) (base : Nat) (word : BitVec 64) :
    load64 (store mem base 8 word) base = word := by
  simp [load64, store]
  bv_decide

theorem load_store32 (mem : Memory) (base : Nat) (word : BitVec 32) :
    load64 (store mem base 4 (word.setWidth 64)) base = pack32 (load64 mem base) word := by
  simp [load64, store, pack32]
  bv_decide

/-- This is a proved byte-level frame law, including all source fields beyond the header. -/
theorem store_frame (mem : Memory) (base count p : Nat) (word : BitVec 64)
    (h : p < base ∨ base + count ≤ p) :
    store mem base count word p = mem p := by
  simp [store, show ¬ (base ≤ p ∧ p < base + count) by omega]

/-- The native `memcpy(&hi, (char *)o + 6, 2)` interpreted as a little-endian UInt16. -/
def savedHi16 (mem : Memory) (base : Nat) : BitVec 16 :=
  (mem (base + 6)).setWidth 16 ||| ((mem (base + 7)).setWidth 16 <<< 8)

theorem savedHi16_pack64 (mem : Memory) (base : Nat) (next : BitVec 64) :
    ((savedHi16 mem base).setWidth 64 <<< 48) ||| next = pack64 (load64 mem base) next := by
  unfold savedHi16 pack64 load64
  bv_decide

/-- Clearing local header bytes 6/7 in `get_next` leaves exactly the low six bytes on this ABI. -/
theorem clear_bytes_unpack64 (mem : Memory) (base : Nat) :
    (mem base).setWidth 64 ||| ((mem (base + 1)).setWidth 64 <<< 8) |||
      ((mem (base + 2)).setWidth 64 <<< 16) ||| ((mem (base + 3)).setWidth 64 <<< 24) |||
      ((mem (base + 4)).setWidth 64 <<< 32) ||| ((mem (base + 5)).setWidth 64 <<< 40) =
    unpack64 (load64 mem base) := by
  unfold unpack64 load64
  bv_decide

def setNext64 (mem : Memory) (base : Nat) (next : BitVec 64) : Memory :=
  store mem base 8 (pack64 (load64 mem base) next)

def setNext32 (mem : Memory) (base : Nat) (next : BitVec 32) : Memory :=
  store mem base 4 (next.setWidth 64)

theorem get_setNext64 (mem : Memory) (base : Nat) (next : BitVec 64) (h : Fits64 next) :
    unpack64 (load64 (setNext64 mem base next) base) = next := by
  rw [setNext64, load_store64, unpack_pack64 _ _ h]

theorem get_setNext32 (mem : Memory) (base : Nat) (next : BitVec 32) :
    unpack32 (load64 (setNext32 mem base next) base) = next := by
  rw [setNext32, load_store32, unpack_pack32]

theorem setNext64_metadata (mem : Memory) (base : Nat) (next : BitVec 64) (h : Fits64 next) :
    tag (load64 (setNext64 mem base next) base) = tag (load64 mem base) ∧
    other (load64 (setNext64 mem base next) base) = other (load64 mem base) := by
  rw [setNext64, load_store64]
  exact pack64_preserves_metadata _ _ h

theorem setNext32_metadata (mem : Memory) (base : Nat) (next : BitVec 32) :
    (load64 (setNext32 mem base next) base) >>> 32 = (load64 mem base) >>> 32 := by
  rw [setNext32, load_store32]
  exact (pack32_preserves_metadata _ _).1

theorem tag_load64 (mem : Memory) (base : Nat) :
    tag (load64 mem base) = mem (base + 7) := by
  unfold tag load64
  bv_decide

theorem other_load64 (mem : Memory) (base : Nat) :
    other (load64 mem base) = mem (base + 6) := by
  unfold other load64
  bv_decide

theorem setNext64_header_bytes (mem : Memory) (base : Nat) (next : BitVec 64)
    (h : Fits64 next) :
    setNext64 mem base next (base + 7) = mem (base + 7) ∧
    setNext64 mem base next (base + 6) = mem (base + 6) := by
  simpa only [tag_load64, other_load64] using setNext64_metadata mem base next h

theorem setNext64_payload (mem : Memory) (base i : Nat) (next : BitVec 64) :
    setNext64 mem base next (base + 8 + i) = mem (base + 8 + i) := by
  apply store_frame
  omega

theorem setNext32_payload (mem : Memory) (base i : Nat) (next : BitVec 32) :
    setNext32 mem base next (base + 8 + i) = mem (base + 8 + i) := by
  apply store_frame
  omega

theorem load64_congr (mem mem' : Memory) (base : Nat)
    (h : ∀ i, i < 8 → mem' (base + i) = mem (base + i)) :
    load64 mem' base = load64 mem base := by
  unfold load64
  have hzero : mem' base = mem base := by simpa using h 0 (by decide)
  rw [hzero, h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem store_other_header (mem : Memory) (base count q : Nat) (word : BitVec 64)
    (hn : count ≤ 8) (hd : base + 8 ≤ q ∨ q + 8 ≤ base) :
    load64 (store mem base count word) q = load64 mem q := by
  apply load64_congr
  intro i hi
  apply store_frame
  omega

/-- Distinct eight-byte-aligned header addresses do not overlap. Allocation and provenance are
separate native obligations; alignment alone does not establish that either block exists. -/
theorem aligned_headers_disjoint (p q : Nat) (hp : p % 8 = 0) (hq : q % 8 = 0)
    (hne : p ≠ q) : p + 8 ≤ q ∨ q + 8 ≤ p := by
  omega

/-- A finite null-terminated list decoded from stored links, without a list-valued ghost tail. -/
def Represents {w : Nat} (read : BitVec w → BitVec w) (head : BitVec w) :
    List (BitVec w) → Prop
  | [] => head = 0
  | p :: tail => head = p ∧ p ≠ 0 ∧ Represents read (read p) tail

theorem represents_frame {read read' : BitVec w → BitVec w} {head : BitVec w}
    {todo : List (BitVec w)} (hr : Represents read head todo)
    (hf : ∀ p ∈ todo, read' p = read p) : Represents read' head todo := by
  induction todo generalizing head with
  | nil => exact hr
  | cons p tail ih =>
    rcases hr with ⟨hhead, hp, ht⟩
    refine ⟨hhead, hp, ?_⟩
    rw [hf p (by simp)]
    exact ih ht (fun q hq => hf q (by simp [hq]))

/-- The two read obligations below are discharged by the concrete byte stores in `push64` and
`push32`, not postulated as axioms about native functions. -/
theorem represents_push {read read' : BitVec w → BitVec w} {head p : BitVec w}
    {todo : List (BitVec w)} (hr : Represents read head todo) (hp : p ≠ 0)
    (hs : read' p = head) (hf : ∀ q ∈ todo, read' q = read q) :
    Represents read' p (p :: todo) := by
  refine ⟨rfl, hp, ?_⟩
  rw [hs]
  exact represents_frame hr hf

def readNext64 (mem : Memory) (p : BitVec 64) := unpack64 (load64 mem p.toNat)
def readNext32 (mem : Memory) (p : BitVec 32) := unpack32 (load64 mem p.toNat)

/-- A fresh dead object's header can hold the existing queue without damaging its suffix.
`hf` bounds the stored pointer; `ha`/`ht` and freshness establish the byte-level frame. -/
theorem push64 (mem : Memory) (p head : BitVec 64) (todo : List (BitVec 64))
    (hr : Represents (readNext64 mem) head todo) (hp : p ≠ 0) (hf : Fits64 head)
    (ha : p.toNat % 8 = 0) (ht : ∀ q ∈ todo, q.toNat % 8 = 0) (fresh : p ∉ todo) :
    Represents (readNext64 (setNext64 mem p.toNat head)) p (p :: todo) := by
  apply represents_push hr hp
  · exact get_setNext64 mem p.toNat head hf
  · intro q hq
    unfold readNext64 setNext64
    rw [store_other_header mem p.toNat 8 q.toNat _ (by decide)]
    exact aligned_headers_disjoint _ _ ha (ht q hq) (by
      intro heq
      have : p = q := BitVec.eq_of_toNat_eq heq
      exact fresh (this ▸ hq))

/-- Four-byte-aligned allocations still have eight-byte headers; their disjointness is a
separate allocation obligation, rather than a consequence of alignment and freshness. -/
theorem push32 (mem : Memory) (p head : BitVec 32) (todo : List (BitVec 32))
    (hr : Represents (readNext32 mem) head todo) (hp : p ≠ 0)
    (hd : ∀ q ∈ todo, p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat) :
    Represents (readNext32 (setNext32 mem p.toNat head)) p (p :: todo) := by
  apply represents_push hr hp
  · exact get_setNext32 mem p.toNat head
  · intro q hq
    unfold readNext32 setNext32
    rw [store_other_header mem p.toNat 4 q.toNat _ (by decide)]
    exact hd q hq

/-- A four-byte allocator prefix need not leave an eight-byte-aligned header. -/
example (mem : Memory) :
    Represents (readNext32 (setNext32 (setNext32 mem 20 0) 4 20)) 4 [4, 20] := by
  apply push32 (setNext32 mem 20 0) 4 20 [20]
  · simp [Represents, readNext32, get_setNext32]
  · decide
  · intro q hq
    have hq : q = 20 := by simpa using hq
    subst q
    decide

/-- Reading the successor before disposal supplies the exact represented suffix. -/
theorem represents_pop {read : BitVec w → BitVec w} {p : BitVec w}
    {todo : List (BitVec w)} (h : Represents read p (p :: todo)) :
    Represents read (read p) todo := h.2.2

theorem pointer_tag64 (p : BitVec 64) (aligned : p &&& 7 = 0) : p &&& 1 = 0 := by
  bv_decide

theorem pointer_tag32 (p : BitVec 32) (aligned : p &&& 3 = 0) : p &&& 1 = 0 := by
  bv_decide

example : (4 : BitVec 32) &&& 1 = 0 := pointer_tag32 4 (by decide)

theorem immediate64 (n : BitVec 64) : ((n <<< 1) ||| 1) &&& 1 = 1 := by
  bv_decide

theorem immediate32 (n : BitVec 32) : ((n <<< 1) ||| 1) &&& 1 = 1 := by
  bv_decide

theorem unbox_box64 (n : BitVec 64) (h : n >>> 63 = 0) :
    ((n <<< 1) ||| 1) >>> 1 = n := by bv_decide

theorem unbox_box32 (n : BitVec 32) (h : n >>> 31 = 0) :
    ((n <<< 1) ||| 1) >>> 1 = n := by bv_decide

/-- The scan may advance to the one-past cursor, but may only read indices below `count`.
The allocation/provenance obligation is additional to this no-wrap arithmetic fact. -/
theorem cursor64 (base : BitVec 64) (count i : Nat) (hi : i ≤ count)
    (hb : base.toNat + 8 * count < 2 ^ 64) :
    (base + BitVec.ofNat 64 (8 * i)).toNat = base.toNat + 8 * i := by
  have hi' : 8 * i < 2 ^ 64 := by omega
  have hb' : base.toNat + 8 * i < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hb']

theorem cursor32 (base : BitVec 32) (count i : Nat) (hi : i ≤ count)
    (hb : base.toNat + 4 * count < 2 ^ 32) :
    (base + BitVec.ofNat 32 (4 * i)).toNat = base.toNat + 4 * i := by
  have hi' : 4 * i < 2 ^ 32 := by omega
  have hb' : base.toNat + 4 * i < 2 ^ 32 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hb']

/-- Out-of-range pointers really do lose bits and can overwrite metadata. -/
example : unpack64 (pack64 0 0x0001000000000000) = 0 := by decide
example : tag (pack64 0 0x8000000000000000) = 0x80 := by decide

end NativeContracts

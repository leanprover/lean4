/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-- A max-heap data structure. -/
structure BinaryHeap (α) (lt : α → α → Bool) where
  arr : Array α

namespace BinaryHeap

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` down to restore the max-heap property. -/
def heapifyDown (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  {a' : Array α // a'.size = a.size} :=
  let left := 2 * i.1 + 1
  let right := left + 1
  have left_le : i ≤ left := Nat.le_trans
    (by rw [Nat.succ_mul, Nat.one_mul]; exact Nat.le_add_left i i)
    (Nat.le_add_right ..)
  have right_le : i ≤ right := Nat.le_trans left_le (Nat.le_add_right ..)
  have i_le : i ≤ i := Nat.le_refl _
  have j : {j : Fin a.size // i ≤ j} := if h : left < a.size then
    if lt a[i] a[left] then ⟨⟨left, h⟩, left_le⟩ else ⟨i, i_le⟩ else ⟨i, i_le⟩
  have j := if h : right < a.size then
    if lt a[j.1] a[right] then ⟨⟨right, h⟩, right_le⟩ else j else j
  if h : i.1 = j then ⟨a, rfl⟩ else
    let a' := a.swap i j
    let j' := ⟨j, by rw [a.size_swap i j]; exact j.1.2⟩
    have : a'.size - j < a.size - i := by
      rw [a.size_swap i j]; sorry
    let ⟨a₂, h₂⟩ := heapifyDown lt a' j'
    ⟨a₂, h₂.trans (a.size_swap i j)⟩
termination_by a.size - i
decreasing_by assumption

@[simp] theorem size_heapifyDown (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  (heapifyDown lt a i).1.size = a.size := (heapifyDown lt a i).2

/-- Core operation for binary heaps, expressed directly on arrays.
Construct a heap from an unsorted array, by heapifying all the elements. -/
def mkHeap (lt : α → α → Bool) (a : Array α) : {a' : Array α // a'.size = a.size} :=
  let rec loop : (i : Nat) → (a : Array α) → i ≤ a.size → {a' : Array α // a'.size = a.size}
  | 0, a, _ => ⟨a, rfl⟩
  | i+1, a, h =>
    let h := Nat.lt_of_succ_le h
    let a' := heapifyDown lt a ⟨i, h⟩
    let ⟨a₂, h₂⟩ := loop i a' ((heapifyDown ..).2.symm ▸ Nat.le_of_lt h)
    ⟨a₂, h₂.trans a'.2⟩
  loop (a.size / 2) a sorry

@[simp] theorem size_mkHeap (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  (mkHeap lt a).1.size = a.size := (mkHeap lt a).2

/-- Core operation for binary heaps, expressed directly on arrays.
Given an array which is a max-heap, push item `i` up to restore the max-heap property. -/
def heapifyUp (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  {a' : Array α // a'.size = a.size} :=
if i0 : i.1 = 0 then ⟨a, rfl⟩ else
  have : (i.1 - 1) / 2 < i := sorry
  let j : Fin a.size := ⟨(i.1 - 1) / 2, Nat.lt_trans this i.2⟩
  if lt a[j] a[i] then
    let a' := a.swap i j
    let ⟨a₂, h₂⟩ := heapifyUp lt a' ⟨j.1, by rw [a.size_swap i j]; exact j.2⟩
    ⟨a₂, h₂.trans (a.size_swap i j)⟩
  else ⟨a, rfl⟩
termination_by i.1
decreasing_by assumption

@[simp] theorem size_heapifyUp (lt : α → α → Bool) (a : Array α) (i : Fin a.size) :
  (heapifyUp lt a i).1.size = a.size := (heapifyUp lt a i).2

/-- `O(1)`. Build a new empty heap. -/
def empty (lt) : BinaryHeap α lt := ⟨#[]⟩

instance (lt) : Inhabited (BinaryHeap α lt) := ⟨empty _⟩
instance (lt) : EmptyCollection (BinaryHeap α lt) := ⟨empty _⟩

/-- `O(1)`. Build a one-element heap. -/
def singleton (lt) (x : α) : BinaryHeap α lt := ⟨#[x]⟩

/-- `O(1)`. Get the number of elements in a `BinaryHeap`. -/
def size {lt} (self : BinaryHeap α lt) : Nat := self.1.size

/-- `O(1)`. Get an element in the heap by index. -/
def get {lt} (self : BinaryHeap α lt) (i : Fin self.size) : α := self.1.get i i.2

/-- `O(log n)`. Insert an element into a `BinaryHeap`, preserving the max-heap property. -/
def insert {lt} (self : BinaryHeap α lt) (x : α) : BinaryHeap α lt where
  arr := let n := self.size;
    heapifyUp lt (self.1.push x) ⟨n, by rw [Array.size_push]; apply Nat.lt_succ_self⟩

@[simp] theorem size_insert {lt} (self : BinaryHeap α lt) (x : α) :
  (self.insert x).size = self.size + 1 := by
  simp [insert, size, size_heapifyUp]

/-- `O(1)`. Get the maximum element in a `BinaryHeap`. -/
def max {lt} (self : BinaryHeap α lt) : Option α := self.1.get? 0

/-- Auxiliary for `popMax`. -/
def popMaxAux {lt} (self : BinaryHeap α lt) : {a' : BinaryHeap α lt // a'.size = self.size - 1} :=
  match e: self.1.size with
  | 0 => ⟨self, by simp [size, e]⟩
  | n+1 =>
    have h0 := by rw [e]; apply Nat.succ_pos
    have hn := by rw [e]; apply Nat.lt_succ_self
    if hn0 : 0 < n then
      let a := self.1.swap ⟨0, h0⟩ ⟨n, hn⟩ |>.pop
      ⟨⟨heapifyDown lt a ⟨0, sorry⟩⟩,
        by simp [size, a]⟩
    else
      ⟨⟨self.1.pop⟩, by simp [size]⟩

/-- `O(log n)`. Remove the maximum element from a `BinaryHeap`.
Call `max` first to actually retrieve the maximum element. -/
def popMax {lt} (self : BinaryHeap α lt) : BinaryHeap α lt := self.popMaxAux

@[simp] theorem size_popMax {lt} (self : BinaryHeap α lt) :
  self.popMax.size = self.size - 1 := self.popMaxAux.2

/-- `O(log n)`. Return and remove the maximum element from a `BinaryHeap`. -/
def extractMax {lt} (self : BinaryHeap α lt) : Option α × BinaryHeap α lt :=
  (self.max, self.popMax)

theorem size_pos_of_max {lt} {self : BinaryHeap α lt} (e : self.max = some x) : 0 < self.size :=
  Decidable.of_not_not fun h: ¬ 0 < self.1.size => by simp [BinaryHeap.max, Array.get?, h] at e

/-- `O(log n)`. Equivalent to `extractMax (self.insert x)`, except that extraction cannot fail. -/
def insertExtractMax {lt} (self : BinaryHeap α lt) (x : α) : α × BinaryHeap α lt :=
  match e: self.max with
  | none => (x, self)
  | some m =>
    if lt x m then
      let a := self.1.set 0 x (size_pos_of_max e)
      (m, ⟨heapifyDown lt a ⟨0, by simp only [Array.size_set, a]; exact size_pos_of_max e⟩⟩)
    else (x, self)

/-- `O(log n)`. Equivalent to `(self.max, self.popMax.insert x)`. -/
def replaceMax {lt} (self : BinaryHeap α lt) (x : α) : Option α × BinaryHeap α lt :=
  match e: self.max with
  | none => (none, ⟨self.1.push x⟩)
  | some m =>
    let a := self.1.set 0 x (size_pos_of_max e)
    (some m, ⟨heapifyDown lt a ⟨0, by simp only [Array.size_set, a]; exact size_pos_of_max e⟩⟩)

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `x ≤ self.get i`. -/
def decreaseKey {lt} (self : BinaryHeap α lt) (i : Fin self.size) (x : α) : BinaryHeap α lt where
  arr := heapifyDown lt (self.1.set i x i.2) ⟨i, by rw [self.1.size_set]; exact i.2⟩

/-- `O(log n)`. Replace the value at index `i` by `x`. Assumes that `self.get i ≤ x`. -/
def increaseKey {lt} (self : BinaryHeap α lt) (i : Fin self.size) (x : α) : BinaryHeap α lt where
  arr := heapifyUp lt (self.1.set i x i.2) ⟨i, by rw [self.1.size_set]; exact i.2⟩

end BinaryHeap

/-- `O(n)`. Convert an unsorted array to a `BinaryHeap`. -/
def Array.toBinaryHeap (lt : α → α → Bool) (a : Array α) : BinaryHeap α lt where
  arr := BinaryHeap.mkHeap lt a

/-- `O(n log n)`. Sort an array using a `BinaryHeap`. -/
@[specialize] def Array.heapSort (a : Array α) (lt : α → α → Bool) : Array α :=
  let gt y x := lt x y
  let rec loop (a : BinaryHeap α gt) (out : Array α) : Array α :=
    match e:a.max with
    | none => out
    | some x =>
      have : a.popMax.size < a.size := by
        simp; exact Nat.sub_lt (BinaryHeap.size_pos_of_max e) Nat.zero_lt_one
      loop a.popMax (out.push x)
    termination_by a.size
    decreasing_by assumption
  loop (a.toBinaryHeap gt) #[]

attribute [simp] Array.heapSort.loop

/--
info: Array.heapSort.loop.eq_1.{u_1} {α : Type u_1} (lt : α → α → Bool) (a : BinaryHeap α fun y x => lt x y) (out : Array α) :
  Array.heapSort.loop lt a out =
    match e : a.max with
    | none => out
    | some x =>
      let_fun this := ⋯;
      Array.heapSort.loop lt a.popMax (out.push x)
-/
#guard_msgs in
#check Array.heapSort.loop.eq_1

attribute [simp] BinaryHeap.heapifyDown

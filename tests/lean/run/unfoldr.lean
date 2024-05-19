notation "#(" a ")" => ⟨a, by decreasing_tactic⟩

def List.unfoldr {α β : Type u} [sz : SizeOf β] (f : (b : β) → Option (α × { b' : β // sizeOf b' < sizeOf b})) (b : β) : List α :=
  match f b with
  | none => []
  | some (a, ⟨b', h⟩) => a :: unfoldr f b'

def tst1 (n : Nat) : List Nat :=
  List.unfoldr (b := n) fun
    | 0 => none
    | b+1 => some (3*n - b*2, #(b))

#guard tst1 10 == [12, 14, 16, 18, 20, 22, 24, 26, 28, 30]

def tst2 (n : Nat) : List Nat :=
  -- Similar example where we provide our custom `SizeOf` instance
  List.unfoldr (sz := ⟨fun b => n - b⟩) (b := 0) fun b =>
    if h : b < n then
      some (b*2, #(b+1))
    else
      none

#guard tst2 10 == [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]

-- More general (and less convenient to use) version that can take an arbitrary well-founded relation.
def List.unfoldr' {α β : Type u} [w : WellFoundedRelation β] (f : (b : β) → Option (α × { b' : β // w.rel b' b})) (b : β) : List α :=
  match f b with
  | none => []
  | some (a, ⟨b', h⟩) => a :: unfoldr' f b'
termination_by b

-- We need the `master` branch to test the following example

def tst3 (n : Nat) : List Nat :=
  List.unfoldr' (b := n) fun
    | 0 => none
    | b+1 => some (3*n - b*2, #(b))

#guard tst3 10 == [12, 14, 16, 18, 20, 22, 24, 26, 28, 30]

def tst4 (n : Nat) : List Nat :=
  List.unfoldr' (w := invImage (fun b => n - b) inferInstance) (b := 0) fun b =>
    if h : b < n then
      some (2*b, #(b+1))
    else
      none

#guard tst4 10 == [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]

inductive DataType
  | TInt
  | TFloat
  | TString

open DataType

inductive DataEntry
  | EInt (i : Int)
  | EFloat (f : Float)
  | EString (s : String)
  | NULL

def NULL := DataEntry.NULL

instance : Coe Int DataEntry where
  coe := DataEntry.EInt

instance : Coe Float DataEntry where
  coe := DataEntry.EFloat

instance : OfNat DataEntry n where
  ofNat := DataEntry.EInt n

instance : OfScientific DataEntry where
  ofScientific m s e := DataEntry.EFloat (OfScientific.ofScientific m s e)

instance : Coe String DataEntry where
  coe := DataEntry.EString

namespace DataEntry

@[simp] def isOf (e : DataEntry) (t : DataType) : Prop :=
  match e, t with
  | EInt _,    TInt    => True
  | EFloat _,  TFloat  => True
  | EString _, TString => True
  | NULL,      _       => True
  | _,         _       => False

-- Needed since the introduction of the fine-grained lemmas
@[simp] theorem isOf_lit (n : Nat) : isOf (no_index (OfNat.ofNat n)) TInt = True := rfl

end DataEntry

abbrev Header := List (DataType × String)

def Header.colTypes (h : Header) : List DataType :=
  h.map fun x => x.1

def Header.colNames (h : Header) : List String :=
  h.map fun x => x.2

abbrev Row := List DataEntry

@[simp] def rowOfTypes : Row → List DataType → Prop
  | [],       []       => True
  | eh :: et, th :: tt => eh.isOf th ∧ rowOfTypes et tt
  | _,        _        => False

@[simp] def rowsOfTypes : List Row → List DataType → Prop
  | row :: rows, types => rowOfTypes row types ∧ rowsOfTypes rows types
  | [],          _     => True

structure DataFrame where
  header     : Header
  rows       : List Row
  consistent : rowsOfTypes rows header.colTypes := by simp

namespace DataFrame

def empty (header : Header := []) : DataFrame :=
  ⟨header, [], by simp⟩

theorem consistentConcatOfConsistentRow
    {df : DataFrame} (row : List DataEntry)
    (hc : rowOfTypes row df.header.colTypes) :
      rowsOfTypes (df.rows.concat row) (Header.colTypes df.header) :=
  match df with
    | ⟨_, rows, hr⟩ => by
      induction rows with
        | nil         => simp at hc; simp [hc]
        | cons _ _ hi => exact ⟨hr.1, hi hr.2 hc⟩

def addRow (df : DataFrame) (row : List DataEntry)
    (h : rowOfTypes row df.header.colTypes := by simp) : DataFrame :=
  ⟨df.header, df.rows.concat row, consistentConcatOfConsistentRow row h⟩

end DataFrame

def h : Header := [(TInt, "id"), (TString, "name")]

def r : List Row := [[1, "alex"]]

-- this no longer works
def df1 : DataFrame := DataFrame.mk h r

-- and this ofc breaks now
def df2 : DataFrame := df1.addRow [2, "juddy"]

-- this doesn't work anymore either
def df3 : DataFrame := DataFrame.empty h |>.addRow [3, "john"]

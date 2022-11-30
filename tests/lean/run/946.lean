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

@[simp] def IsOf (e : DataEntry) (t : DataType) : Prop :=
  match e, t with
  | EInt _,    TInt    => True
  | EFloat _,  TFloat  => True
  | EString _, TString => True
  | NULL,      _       => True
  | _,         _       => False

end DataEntry

abbrev Header := List (DataType × String)

def Header.colTypes (h : Header) : List DataType :=
  h.map fun x => x.1

def Header.colNames (h : Header) : List String :=
  h.map fun x => x.2

abbrev Row := List DataEntry

@[simp] def RowOfTypes : Row → List DataType → Prop
  | [],       []       => True
  | eh :: et, th :: tt => eh.IsOf th ∧ RowOfTypes et tt
  | _,        _        => False

@[simp] def RowsOfTypes : List Row → List DataType → Prop
  | row :: rows, types => RowOfTypes row types ∧ RowsOfTypes rows types
  | [],          _     => True

structure DataFrame where
  header     : Header
  rows       : List Row
  consistent : RowsOfTypes rows header.colTypes := by simp

namespace DataFrame

def empty (header : Header := []) : DataFrame :=
  ⟨header, [], by simp⟩

theorem consistent_concat_of_consistent_row
    {df : DataFrame} (row : List DataEntry)
    (hc : RowOfTypes row df.header.colTypes) :
      RowsOfTypes (df.rows.concat row) (Header.colTypes df.header) :=
  match df with
    | ⟨_, rows, hr⟩ => by
      induction rows with
        | nil         => simp at hc; simp [hc]
        | cons _ _ hi => exact ⟨hr.1, hi hr.2 hc⟩

def addRow (df : DataFrame) (row : List DataEntry)
    (h : RowOfTypes row df.header.colTypes := by simp) : DataFrame :=
  ⟨df.header, df.rows.concat row, consistent_concat_of_consistent_row row h⟩

end DataFrame

def h : Header := [(TInt, "id"), (TString, "name")]

def r : List Row := [[1, "alex"]]

-- this no longer works
def df1 : DataFrame := DataFrame.mk h r

-- and this ofc breaks now
def df2 : DataFrame := df1.addRow [2, "juddy"]

-- this doesn't work anymore either
def df3 : DataFrame := DataFrame.empty h |>.addRow [3, "john"]

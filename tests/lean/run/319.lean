class Class.{u} where
  dummy : PUnit.{u}

def notWork [Class.{u}] : PUnit := Class.dummy
def alsoNotWork [Class.{1}] : PUnit := Class.dummy
def work [Class.{u}] : PUnit.{u} := Class.dummy
def alsoWork [Class.{u}] := Class.dummy.{u}


class Category.{v, u} (Ob : Type u) where
  Hom : Ob → Ob → Type v

variable (C : Type u) [Category.{v} C] (X : C)
#check (Category.Hom X X)

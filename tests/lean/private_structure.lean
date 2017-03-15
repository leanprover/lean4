namespace foo
private structure point :=
(x : nat) (y : nat)

definition bla := point
definition mk : bla := point.mk 10 10
#check bla
#check point
#check point.mk
#check point.rec
#check point.rec_on
#check point.cases_on
#check point.x
#check point.y

end foo

open foo

-- point is not visible anymore

#check bla
#check point
#check point.mk
#check point.rec
#check point.rec_on
#check point.cases_on
#check point.no_confusion
#check point.x
#check point.y

set_option pp.all true
#print bla

#check (⟨1, 2⟩ : bla)
#check mk

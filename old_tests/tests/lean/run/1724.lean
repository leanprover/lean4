example (h : ¬ true) : false :=
by  simp * at *

example (h : true) (h' : true → false) : false :=
by simp * at *

example (p : Prop) (h : p) (h' : p → false) : false :=
by simp * at *

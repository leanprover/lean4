section t

parameter t : Type

inductive eqt : t -> t -> Prop
| refl : forall x : t, eqt x x

#check eqt

end t

#check eqt

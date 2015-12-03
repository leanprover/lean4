constant P : Type₁
constant P_sub : subsingleton P
attribute P_sub [instance]
constant q : P → Prop

#congr q

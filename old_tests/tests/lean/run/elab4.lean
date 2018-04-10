#check λ (A : Type) (a b c d : A) (H1 : a = b) (H2 : c = b) (H3 : d = c),
calc  a  = b : H1
     ... = c : eq.symm H2
     ... = d : eq.symm H3

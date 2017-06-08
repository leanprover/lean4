#eval format!"hi"
#eval format! "hi"
#eval format!"hi\nhi"
#eval format!"{1}+{1}"
#eval format!"{1+1}"
#eval format!"{{{1+1}}"
#eval format!"a{1}"
#eval format!"{1}a"
#eval format!"}"

#check λ α, format!"{α}"

#eval format!"{"
#eval format!"{}"
#eval format!"{1+}"

#eval sformat!"a{'b'}c"

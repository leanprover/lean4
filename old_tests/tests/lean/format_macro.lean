#eval to_string $ format!"hi"
#eval to_string $ format! "hi"
#eval to_string $ format!"hi\nhi"
#eval to_string $ format!"{1}+{1}"
#eval to_string $ format!"{1+1}"
#eval to_string $ format!"{{{1+1}}"
#eval to_string $ format!"a{1}"
#eval to_string $ format!"{1}a"
#eval to_string $ format!"}"

#check λ α, format!"{α}"

#eval format!"{"
#eval format!"{}"
#eval format!"{1+}"

#eval sformat!"a{'b'}c"

example (h : false) : 10000000 = 20000000 :=
begin
  try {simp},
  contradiction
end

example (h : false) (x : nat) : x + 10000000 = x + 20000000 :=
begin
  try {simp},
  contradiction
end

example (h : false) (x y : nat) : x + y + 10000000 = x + y + 20000000 :=
begin
  try {simp},
  contradiction
end

example (h : false) : "hello" = "world" :=
begin
  try {simp},
  contradiction
end

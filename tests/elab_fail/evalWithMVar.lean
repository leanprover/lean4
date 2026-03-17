

def c {α} : Sum α Nat :=
Sum.inr 10

def Sum.someRight {α β} (s : Sum α β) : Option β :=
match s with
| Sum.inl _ => none
| Sum.inr b => some b

#check Sum.someRight c

#eval Sum.someRight c

#check Sum.someRight (s := c)

#check c.someRight

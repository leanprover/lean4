namespace foo

meta mutual def even, odd
with even : nat → bool
| 0     := tt
| (n+1) := odd n
with odd : nat → bool
| 0     := ff
| (n+1) := even n

#eval even 10
#eval even 11

end foo

#print foo.even._main
#print foo.odd._main

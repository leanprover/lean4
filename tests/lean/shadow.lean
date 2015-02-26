open nat

variable a : nat

-- The variable 'a' in the following definition is not the variable 'a' above
definition tadd : nat → nat → nat
| tadd zero     b := b
| tadd (succ a) b := succ (tadd a b)

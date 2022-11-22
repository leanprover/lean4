abbrev f : Nat → Nat
  | 0 => 0
  | n + 1 => f n
termination_by _ n => n

mutual
abbrev f1 : Nat → Nat
  | 0 => 0
  | n + 1 => f1 n
end
termination_by _ n => n

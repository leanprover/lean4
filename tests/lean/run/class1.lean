import logic data.prod data.num
open prod inhabited

definition H : inhabited (Prop × num × (num → num)) := _

print H
